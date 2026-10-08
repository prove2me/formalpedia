-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_theorem_4_1
-- name    : GraphonMF.SparseLLN.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:44.988529+00:00
-- url     : https://prove2.me/theorems/01bc8230-33b9-407e-b136-8900013b7d54
-- title:
--   Theorem 4.1 — law of large numbers for percolated particle systems
-- statement:
--   Consider the percolated system (4.1), with graphon limit (4.2). Assume Conditions 2.2(a), 4.1, and 4.2: the initial laws vary continuously in $W_2$ on finitely many intervals, the drift and state-only diffusion satisfy the stated boundedness and regularity conditions, $n\beta_n\to\infty$, and the Bernoulli edge means are $\beta_nG_n(i/n,j/n)$ with $G_n\to G$ in cut norm. Write $\mu^n=n^{-1}\sum_i\delta_{X_i^n}$ and $\bar\mu=\int_I\mathcal L(X_u)\,du$. Then
--
--   $$\mu^n\xrightarrow{\mathbb P}\bar\mu\quad\text{in }\mathcal P(\mathcal C_d).$$
--
--   If Condition 2.2(b), the almost-everywhere sectional continuity of $G$, also holds, then
--
--   $$\frac1n\sum_{i=1}^{n}\mathbb E\|X_i^n-X_{i/n}\|_{*,T}^{2}\longrightarrow0.$$
--
--   The first clause is an empirical-law limit; the additional regularity gives a direct mean-square coupling to the continuum particles.
--
--   **Formalization Note** The statement includes both clauses, with 2.2(b) required only for the second. Empirical measures are defined for $n\ge1$ and indexed by $n+1$ in Lean. Convergence in probability uses the weak topology on probability measures; expectations use lower integrals. The positive time horizon and dimension are explicit standing conventions.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3597–3598, Theorem 4.1, (4.3)–(4.4); https://doi.org/10.1214/22-AAP1901

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Theorem 4.1, pp. 3597–3598: empirical-law LLN and, under 2.2(b), pathwise mean-square convergence. -/
theorem theorem_4_1
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (N : ℕ) (J : Fin N → Set GraphonMF.Stability.I)
    (h22a : Cond22a (initialLaw P X0) J)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j))
    (h42 : Cond42 P X0 B ξ Gs β G)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n (Xn n)) :
    ConvergesInProbability P (empiricalSeq Xn) (solutionMixture hX) ∧
      (Cond22b G J → Tendsto
        (fun n => errorAvg P X (n + 1) (Xn (n + 1))) atTop (𝓝 (0 : ℝ≥0∞))) := by sorry

end GraphonMF.SparseLLN
