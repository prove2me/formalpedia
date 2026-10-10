-- Prove2me | Theorems.Thm_FullyCoupledSDE_DiffApprox_lemma_4_1_mollifier
-- name    : FullyCoupledSDE.DiffApprox.lemma_4_1_mollifier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:37.889697+00:00
-- url     : https://prove2.me/theorems/3bed2d7d-4466-40d2-9a68-4ede2708e65b
-- title:
--   Lemma 4.1, p. 1222 — mollifier estimates: |f − f_n| ≤ C0 n^{−ϑ}(1+|x|^m), |∂_t f_n| + |∇²_y f_n| ≤ C0 n^{2−ϑ}(1+|x|^m)
-- statement:
--   Let $\rho_1:\mathbb R\to[0,1]$ and $\rho_2:\mathbb R^{d_2}\to[0,1]$ be smooth radial kernels with $\int\rho_1=\int\rho_2=1$, such that for every $k\ge1$ there is $C_k>0$ with $|\rho_1^{(k)}(r)|\le C_k\rho_1(r)$ and $|\nabla^k\rho_2(y)|\le C_k\rho_2(y)$. Let $0<\vartheta\le2$ and assume moreover that the kernels have the finite moments $\int_{\mathbb R}|r|^{\vartheta/2}\rho_1(r)\,dr<\infty$ and $\int_{\mathbb R^{d_2}}|z|^{\vartheta}\rho_2(z)\,dz<\infty$. For $n\in\mathbb N^*$ put $\rho^n_1(r)=n^2\rho_1(n^2r)$, $\rho^n_2(z)=n^{d_2}\rho_2(nz)$ and
--   $$f_n(t,x,y)=\int_{\mathbb R^{d_2+1}}f(t-s,x,y-z)\rho^n_2(z)\rho^n_1(s)\,dz\,ds.\tag{4.1}$$
--   Let $0<\delta\le1$ and $f\in C^{\vartheta/2,\delta,\vartheta}_p$. Then there are $C_0,m>0$ such that, for every $n\ge1$ and every $t,x,y$,
--   $$|f(t,x,y)-f_n(t,x,y)|\le C_0n^{-\vartheta}(1+|x|^m),\tag{4.2}$$
--   $f_n$ is differentiable in $t$ and twice differentiable in $y$, and
--   $$|\partial_tf_n(t,x,y)|+|\nabla^2_yf_n(t,x,y)|\le C_0n^{2-\vartheta}(1+|x|^m).\tag{4.3}$$
--
--   The constants do not depend on $n$. The lemma lets the proofs of the fluctuation estimates replace a coefficient that is only Hölder in $(t,y)$ by a smooth one, at a cost measured in powers of $n$.
--
--   **Formalization Note.** (4.1) evaluates $f$ at negative times, so $f$ is given on $\mathbb R\times\mathbb R^{d_1}\times\mathbb R^{d_2}$ with the $C^{\vartheta/2,\delta,\vartheta}_p$ bounds on all of $\mathbb R$ (any bounded Hölder extension in time, e.g. $f(t)=f(0)$ for $t<0$, has them). The page writes $\rho^n_1(y):=n^2\rho_1(n^2r)$, read as $\rho^n_1(r)$. The sup norms of (4.2)–(4.3) are pointwise bounds for all $(t,y)$; $\nabla^2_y$ is the operator norm of the second Fréchet derivative. The integral (4.1) is an iterated Lebesgue integral. $f$ is real-valued. The two moment conditions on $\rho_1,\rho_2$ are not written on the page; they are what the proof's last step $\int(|s|^{\vartheta/2}+|z|^\vartheta)\rho^n_2(z)\rho^n_1(s)\,dz\,ds\le Cn^{-\vartheta}$ (p. 1222) uses, and without them (4.2) fails: for the Cauchy-type kernel $\rho_2(z)=c_{d_2}(1+|z|^2)^{-(d_2+1)/2}$, which satisfies every printed condition, and $f=\cos y_1$, one gets $f-f_n=1-e^{-1/n}\sim n^{-1}$ at $y=0$, not $O(n^{-\vartheta})$ for $\vartheta>1$.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1222, §4.1, (4.1) and Lemma 4.1, (4.2)–(4.3)

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory
open scoped ContDiff

/-- Lemma 4.1, p. 1222. Mollifier estimates (4.2)–(4.3) for `f ∈ C^{ϑ/2,δ,ϑ}_p`, `0 < ϑ ≤ 2`,
`0 < δ ≤ 1` (here `f` is given on all of `ℝ` in time, as (4.1) requires; the kernels have the
finite moments `∫|r|^{ϑ/2}ρ_1 < ∞`, `∫|z|^ϑρ_2 < ∞` that the proof's last step uses). -/
theorem lemma_4_1_mollifier {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (ρ1 : ℝ → ℝ) (ρ2 : FullyCoupledSDE.Poisson.E d2 → ℝ)
    (hρ1_smooth : ContDiff ℝ ∞ ρ1) (hρ1_radial : ∀ r, ρ1 (-r) = ρ1 r)
    (hρ1_range : ∀ r, ρ1 r ∈ Set.Icc (0 : ℝ) 1) (hρ1_int : ∫ r, ρ1 r = 1)
    (hρ1_deriv : ∀ k : ℕ, 1 ≤ k → ∃ Ck > (0 : ℝ), ∀ r, |iteratedDeriv k ρ1 r| ≤ Ck * ρ1 r)
    (hρ2_smooth : ContDiff ℝ ∞ ρ2) (hρ2_radial : ∀ z z' : FullyCoupledSDE.Poisson.E d2, ‖z‖ = ‖z'‖ → ρ2 z = ρ2 z')
    (hρ2_range : ∀ z, ρ2 z ∈ Set.Icc (0 : ℝ) 1) (hρ2_int : ∫ z, ρ2 z = 1)
    (hρ2_deriv : ∀ k : ℕ, 1 ≤ k → ∃ Ck > (0 : ℝ), ∀ z, ‖iteratedFDeriv ℝ k ρ2 z‖ ≤ Ck * ρ2 z)
    (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2)
    (hρ1_mom : Integrable (fun r : ℝ => |r| ^ (ϑ / 2) * ρ1 r))
    (hρ2_mom : Integrable (fun z : FullyCoupledSDE.Poisson.E d2 => ‖z‖ ^ ϑ * ρ2 z))
    (f : ℝ → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ) (hf : CpT (ϑ / 2) δ ϑ f) :
    ∃ C0 > (0 : ℝ), ∃ m > (0 : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ (t : ℝ) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2),
      |f t x y - mollify ρ1 ρ2 f n t x y| ≤ C0 * (n : ℝ) ^ (-ϑ) * (1 + ‖x‖ ^ m) ∧
      DifferentiableAt ℝ (fun t' => mollify ρ1 ρ2 f n t' x y) t ∧
      ContDiff ℝ 2 (fun y' => mollify ρ1 ρ2 f n t x y') ∧
      |deriv (fun t' => mollify ρ1 ρ2 f n t' x y) t| +
          ‖iteratedFDeriv ℝ 2 (fun y' => mollify ρ1 ρ2 f n t x y') y‖ ≤
        C0 * (n : ℝ) ^ (2 - ϑ) * (1 + ‖x‖ ^ m) := by sorry

end FullyCoupledSDE.DiffApprox
