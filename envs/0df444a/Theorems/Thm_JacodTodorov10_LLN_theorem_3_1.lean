-- Prove2me | Theorems.Thm_JacodTodorov10_LLN_theorem_3_1
-- name    : JacodTodorov10.LLN.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:19:30.140814+00:00
-- url     : https://prove2.me/theorems/1b38a245-d70b-4360-81d4-079333c87880
-- title:
--   Theorem 3.1 — U(F, kₙ) → U(F) in probability for the Skorokhod topology
-- statement:
--   Let $X$ be an Itô semimartingale
--   $$X_t=X_0+\int_0^tb_s\,ds+\int_0^t\sigma_s\,dW_s+\int_0^t\!\!\int_E\delta(s,z)1_{\{|\delta(s,z)|\le1\}}(\mu-\nu)(ds,dz)+\int_0^t\!\!\int_E\delta(s,z)1_{\{|\delta(s,z)|>1\}}\mu(ds,dz),$$
--   driven by a Brownian motion $W$ and a Poisson random measure $\mu$ with compensator $\nu(ds,dz)=ds\otimes\lambda(dz)$, with volatility $c_t=\sigma_t^2$. Assume (H-$r$) for some $r<2$ and (K-$v$), and let the scheme $(\Delta_n,u_n,k_n)$ satisfy (3.3). Let $F$ be a Borel function on $\mathbb R\times(0,\infty)^2$ which is continuous at each point of $R\times(0,\infty)^2$ for some $R\in\mathcal R$ (an open set with finite complement containing every value that $\Delta X$ takes with positive probability). Suppose one of the following holds:
--
--   1. $F(x,y,z)=0$ for $|x|\le\varepsilon$, for some $\varepsilon>0$;
--   2. $r=0$;
--   3. $|F(x,y,z)|\le K|x|^r(1+y+z)$ for $|x|\le\varepsilon$, for some $\varepsilon,K>0$.
--
--   Then, almost surely, $U(F)_t=\sum_{s\le t}F(\Delta X_s,c_{s-},c_s)1_{\{\Delta X_s\ne0\}}$ converges absolutely for every $t$, and the observable processes
--   $$U(F,k_n)_t=\sum_{i=k_n+1}^{[t/\Delta_n]-k_n}F\big(\Delta^n_iX,\widehat c(k_n)_{i-k_n-1},\widehat c(k_n)_i\big)1_{\{|\Delta^n_iX|>u_n\}}$$
--   converge in probability, for the Skorokhod topology, to $U(F)$.
--
--   This is the law of large numbers behind the authors' tests: with $F$ vanishing exactly when $y=z$, $U(F)_T$ is positive precisely when $X$ and its volatility jump together on $[0,T]$, and $U(F,k_n)_T$ estimates it from discrete observations.
--
--   **Formalization Note** The model is stated jointly with the representation (8.1) of the process $Z$ of (K-$v$), driven by the same Poisson measure and a second Brownian motion $W'$ independent of $W$, as §8.1 does ("it is no restriction"); clause (b) of (H-·) is not imposed on $Z$. Convergence in probability for the Skorokhod topology is the subsequence criterion. $F$ is a Borel function on $\mathbb R^3$; its values at $y\le0$ or $z\le0$ are irrelevant since $\widehat c(k_n)_i>0$ and $c_t>0$ a.s. In (c), $|x|^r$ is the real power; at $r=0$ it reads $|F|\le K(1+y+z)$, already covered by (b). $\Delta_n\to0$ is part of (3.3) here. The identity (2.1) and the path properties are almost sure.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §3.1, Theorem 3.1, p. 5; model §2, pp. 3–4; (3.1)–(3.6), pp. 4–5

import Mathlib
import Definitions.Def_JacodTodorov10_LLN_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- **Theorem 3.1** of Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1
(Ann. Appl. Probab. 20 (2010)), §3.1, p. 5. Assume (H-r) for some `r < 2`, (K-v) and (3.3), and let
`F` be a Borel function which is continuous at each point of `R × ℝ*₊²` for some `R ∈ 𝓡`. If one of
(a) `F(x, y, z) = 0` for `|x| ≤ ε`, some `ε > 0`; (b) `r = 0`;
(c) `|F(x, y, z)| ≤ K|x|^r(1 + y + z)` for `|x| ≤ ε`, some `ε, K > 0`
holds, then the processes `U(F, k_n)` converge in probability, for the Skorokhod topology, to `U(F)`.
The conclusion also records that the series `U(F)_t` converges absolutely, a.s., for all `t`.

Formalization Note: the model is `IsModel` ((2.1) driven by an `(𝓕_t)`-Brownian motion and an
`(𝓕_t)`-Poisson random measure) together with the representation (8.1) of `Z` inside `KAssume`,
with the same Poisson measure and a second Brownian motion `W'` (§8.1, p. 24: "it is no
restriction"); (K-v)(a) does not impose clause (b) of (H-·) on `Z`. Convergence in probability for
the Skorokhod topology is the subsequence criterion `TendstoInProbJ1`. `F` is a function on `ℝ³`,
Borel there; its values at `y ≤ 0` or `z ≤ 0` are irrelevant since `ĉ > 0` and `c > 0` a.s.
In (c), `|x|^r` is the real power, which at `r = 0` gives `|F| ≤ K(1 + y + z)`, a case already
covered by (b). `Δ_n → 0` is part of `Scheme.Cond33`. -/
theorem theorem_3_1 {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (lam : Measure E) [SigmaFinite lam] (M : Data Ω E) (r v : ℝ) (S : Scheme) (ϖ ρ : ℝ)
    (F : ℝ → ℝ → ℝ → ℝ)
    (hM : IsModel 𝓕 P lam M) (hH : HAssume 𝓕 P lam r M) (hr : r < 2)
    (hK : KAssume 𝓕 P lam v M) (hS : S.Cond33 ϖ ρ)
    (hFmeas : Measurable (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2))
    (hFcont : ∃ R : Set ℝ, InR P M.X R ∧ ∀ x ∈ R, ∀ y z : ℝ, 0 < y → 0 < z →
      ContinuousAt (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) (x, y, z))
    (hcase : (∃ ε > 0, ∀ x y z : ℝ, |x| ≤ ε → 0 < y → 0 < z → F x y z = 0) ∨ r = 0 ∨
      (∃ ε > 0, ∃ K > 0, ∀ x y z : ℝ, |x| ≤ ε → 0 < y → 0 < z →
        |F x y z| ≤ K * |x| ^ r * (1 + y + z))) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : {s : ℝ≥0 // 0 < s ∧ s ≤ t ∧ pjump M.X s ω ≠ 0} =>
        F (pjump M.X s ω) (cLeft M.σ s ω) (c M.σ s ω))) ∧
    TendstoInProbJ1 P (fun n => UFk S M.X F n) (UF M.X M.σ F) := by sorry

end JacodTodorov10.LLN
