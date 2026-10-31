-- Prove2me | Theorems.Thm_MonoIncExtrap_lemma_6
-- name    : MonoIncExtrap.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:27.225647+00:00
-- url     : https://prove2.me/theorems/a340fe10-1871-4671-a39e-a7da58f63196
-- title:
--   Lemma 6, p.17 — trial points stay in $\widehat{\mathcal S}$
-- statement:
--   Assume the standing assumptions of §2: $\gamma_0>0$, $\delta\in(0,1)$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $\epsilon>0$, $x^0\in\mathrm{dom}\,B$, Assumption 1 with $\mu>0$, and let $x^*$ be the solution of (1). For $\gamma>0$ let
--   $$
--   x^{t+1}(\gamma)=(I+\gamma B)^{-1}\bigl(x^t+\alpha_t(\gamma)(x^t-x^{t-1})-\gamma(F(x^t)+\beta_t(\gamma)(F(x^t)-F(x^{t-1})))\bigr),
--   $$
--   with $\beta_t(\gamma)=\frac{\gamma_{t-1}}{\gamma}(1+\frac{2\mu\gamma_{t-1}}{1-\eta})^{-1}$ and $\alpha_t(\gamma)=\eta\gamma\beta_t(\gamma)/\gamma_{t-1}$. Let $L_{\mathcal S}>0$ be a Lipschitz constant of $F$ on $\mathcal S$. If $x^t,x^{t-1}\in\mathcal S$, then
--   $$
--   x^{t+1}(\gamma)\in\widehat{\mathcal S}\qquad\text{for every }0<\gamma\le\gamma_0.
--   $$
--
--   So every point the line search tries lies in the set on which $L_{\widehat{\mathcal S}}$ is valid.
--
--   **Formalization Note** Here $t=s+1$, and $\gamma=$ `g`.
--
--   Differences from the source:
--   - encoding: $F$ is a point-valued operator on $\mathrm{cl}(\mathrm{dom}\,B)$ → a total map on $\mathbb R^n$, constrained only on $\mathrm{cl}(\mathrm{dom}\,B)$; reason: values of $F$ elsewhere never enter $F+B$ or a run, since iterates lie in $\mathrm{dom}\,B$
--   - encoding: Assumption 1(d), the resolvent of $\gamma B$ can be exactly evaluated → a family $J$ with $J_\gamma=(I+\gamma B)^{-1}$ for every $\gamma>0$; reason: the assumption has no mathematical content; the family exists and is unique on $\gamma>0$
--   - generalization: $1\le t\in\mathbb T-1$, so $x^{t+1}$ has been generated → only iterations before $t$ have run (`IsPrefix` at $t-1$); reason: the data $x^{t-1},x^t,\gamma_{t-1}$ of (53) exist already, the proof does not use $x^{t+1}$, and the proof of Lemma 7 applies Lemma 6 before $x^{t+1}$ is generated; the printed range is a special case
--   - generalization: $L_{\mathcal S}$ is the constant given by Lemma 1, for some choice → every positive Lipschitz constant of $F$ on $\mathcal S$; reason: the proof uses only that bound, and Lemma 1 supplies such a constant
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, Lemma 6, p.17

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-- **Lemma 6.** arXiv:2206.00973v3, Lemma 6, p.17. If `x^{t−1}, x^t ∈ S` then `x^{t+1}(g) ∈ Ŝ` for
every `0 < g ≤ γ0`, where `x^{t+1}(g)` is the point (53) and `Ŝ` is built from a Lipschitz constant
`L_S` of `F` on `S`.

**Formalization Note.** Here `t = s + 1`. The hypothesis is `IsPrefix I x γ n' s`, i.e. iterations
before `t` have run, instead of the printed `t ∈ 𝕋 − 1` (`x^{t+1}` generated): the data
`x^{t−1}, x^t, γ_{t−1}` of (53) exist already, and the proof of Lemma 7 applies Lemma 6 before
`x^{t+1}` is generated. -/
theorem lemma_6 {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg1.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg1.Standing B I xstar)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {γ : ℕ → ℝ} {n' : ℕ → ℕ} {s : ℕ}
    (hx : Alg1.IsPrefix I x γ n' s)
    {LS : ℝ} (hLS : 0 < LS)
    (hLip : IsLipschitzOn I.F (Alg1.setS B xstar (I.r0 xstar) I.ν) LS)
    (hs : x s ∈ Alg1.setS B xstar (I.r0 xstar) I.ν)
    (hs' : x (s + 1) ∈ Alg1.setS B xstar (I.r0 xstar) I.ν)
    {g : ℝ} (hg : 0 < g) (hg' : g ≤ I.γ0) :
    I.trial (x s) (x (s + 1)) (γ s) g ∈ Alg1.setShat B xstar (I.r0 xstar) I.ν I.γ0 LS := by sorry

end MonoIncExtrap
