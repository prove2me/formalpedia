-- Prove2me | Theorems.Thm_MasulloRH_global_theta_dilation_cocycle
-- name    : MasulloRH.global_theta_dilation_cocycle
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:37:26.710506+00:00
-- url     : https://prove2.me/theorems/c1ff11dd-2ff5-4c44-95d6-a4684346d8d5
-- title:
--   The global theta dilation cocycle, its prime-power trace, and endpoint energy growth
-- statement:
--   Let $\rho(u)=1_{u\le0}+r(u)$ with $r\in L^1(\mathbb R)$. On $t>0$, let $m(h)=\int_0^\infty h(t)\,dt$, $\theta h(t)=\sum_{n\ge1}h(nt)$, $U_s h(t)=e^{-s/2}h(e^{-s}t)$ and $R_\rho h(t)=\theta h(t)-m(h)\rho(\log t)/t$. For integrable $h$ the commutator factors through its mass:
--   $$R_\rho(U_s h)(t)-U_s(R_\rho h)(t)=m(h)\,d_s(t),\qquad d_s(t)=e^{s/2}\frac{\rho(\log t-s)-\rho(\log t)}{t}.$$
--   Summability of the two reindexed theta series is equivalent. The output $d_s$ is integrable for $dt$ and its mass is $s e^{s/2}$. For $p>1$ and any real $s$, summing the masses at $s-j\log p$, $j\ge1$, gives
--   $$e^{s/2}\left(\frac{s}{\sqrt p-1}-\frac{\sqrt p\log p}{(\sqrt p-1)^2}\right).$$
--   There is also a lower bound for the actual dilation-averaged range on a shrinking interval. Suppose $\rho=1$ on $(-\infty,L]$ and $\rho=0$ on $(H,\infty)$. Choose $A>0$ and a real test $\varphi$ supported where $x<\log A-H$. Put $M=\int\varphi(x)e^{x/2}dx$ and $K_j(t)=\int\varphi(x)d_{x-j\log p}(t)dx$. For all sufficiently large $j$,
--   $$\int_{A/p^j}^{2A/p^j}\max(t,t^{-1})(1+\log^2t)|K_j(t)|^2\,dt\ \ge\ \frac{(\log p)^2 M^2}{32 A^2}j^2p^j.$$
--   Thus if $M\ne0$, the local energy grows for every such fixed transition profile.
-- source:
--   Global theta counterterm under half-density dilation, investigated for the endpoint-weighted rational logarithmic chart of the Masullo RH mission. The signed-slab calculation uses the same half-line boundary convention as the existing MasulloRH.halfspace_shift_boundary_integral theorem.

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Set Filter

theorem MasulloRH.global_theta_dilation_cocycle (r : ℝ → ℝ) (hr : Integrable r) :
    let ρ (u : ℝ) := (if u≤0 then (1:ℝ) else 0) + r u
    let m (g : ℝ → ℝ) := ∫ t in Ioi (0:ℝ), g t
    let θ (g : ℝ → ℝ) (t : ℝ) := ∑' n : ℕ, g (((n:ℝ)+1)*t)
    let U (s : ℝ) (g : ℝ → ℝ) (t : ℝ) := Real.exp (-s/2) * g (Real.exp (-s)*t)
    let R (g : ℝ → ℝ) (t : ℝ) := θ g t - m g * ρ (Real.log t) / t
    let d (b t : ℝ) := Real.exp (b/2)*(ρ (Real.log t-b)-ρ (Real.log t))/t
    (∀ (h : ℝ → ℝ) (s : ℝ), IntegrableOn h (Ioi 0) →
      IntegrableOn (U s h) (Ioi 0) ∧ m (U s h) = Real.exp (s/2)*m h ∧
      (∀ t : ℝ, 0<t →
        (Summable (fun n : ℕ => U s h (((n:ℝ)+1)*t)) ↔
          Summable (fun n : ℕ => h (((n:ℝ)+1)*(Real.exp (-s)*t)))) ∧
        R (U s h) t - U s (R h) t = m h * d s t) ∧
      IntegrableOn (fun t => R (U s h) t - U s (R h) t) (Ioi 0) ∧
      m (fun t => R (U s h) t - U s (R h) t) = m h * (s*Real.exp (s/2))) ∧
    (∀ s : ℝ, IntegrableOn (d s) (Ioi 0) ∧ m (d s) = s*Real.exp (s/2)) ∧
    (∀ p s : ℝ, 1<p →
      HasSum (fun j : ℕ => m (d (s-((j:ℝ)+1)*Real.log p)))
        (Real.exp (s/2)*(s/(Real.sqrt p-1) - Real.log p*Real.sqrt p/(Real.sqrt p-1)^2))) ∧
    (∀ (φ : ℝ → ℝ) (p A L H : ℝ), 1<p → 0<A →
      (∀ u : ℝ, u≤L → ρ u=1) → (∀ u : ℝ, H<u → ρ u=0) →
      (∀ x : ℝ, φ x≠0 → x<Real.log A-H) →
      let M := ∫ x : ℝ, φ x*Real.exp (x/2)
      let K (j : ℕ) (t : ℝ) := ∫ x : ℝ, φ x*d (x-(j:ℝ)*Real.log p) t
      ∀ᶠ j : ℕ in atTop, ((Real.log p)^2/(32*A^2))*M^2*(j:ℝ)^2*p^j ≤
        ∫ t in Icc (A/p^j) (2*A/p^j), (max t (1/t)*(1+(Real.log t)^2))*|K j t|^2) := by sorry
