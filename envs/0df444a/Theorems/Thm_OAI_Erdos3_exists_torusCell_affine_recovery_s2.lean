-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_torusCell_affine_recovery_s2
-- name    : OAI.Erdos3.exists_torusCell_affine_recovery_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:40:35.361328+00:00
-- url     : https://prove2.me/theorems/7346b2fa-a501-4795-883e-ad54760cf4ad
-- title:
--   Integer roundings of a bounded integer linear map on one torus grid cell differ from the integer lift by a constant
-- statement:
--   Let $\Omega$ be a type, $d, m, q$ natural numbers with $q \ge 8$, $S \subseteq \Omega$, $M$ an integer $m \times d$ matrix ($M : \operatorname{Fin} m \to \operatorname{Fin} d \to \mathbb{Z}$), $a : \operatorname{Fin} d \to \operatorname{Fin} q$ a grid cell label, $x : \Omega \to \mathbb{R}^d$, $\beta : \Omega \to \mathbb{Z}^m$, and $K$ a real number. Let $\Phi$ = `torusGridKernel d q hq a`, OpenAI's patch kernel on $\mathbb{R}^d$ (a normalized local tent kernel at scale $1/q$ translated to the grid cell $a$), and let $x_0$ = `torusGridCenter q a` $= (a_i / q)_i$. For $y \in \mathbb{R}^d$, `Φ.periodicValue y` is OpenAI's periodization of $\Phi$ at $y$, and `Φ.integerLift y` $\in \mathbb{Z}^d$ is an integer vector $b$ with $\Phi(b - y) \ne 0$ if one exists (chosen by OpenAI), and $0$ otherwise.
--
--   Assume:
--   - $\sum_j |M_{ij}| \le K$ for every row $i$, and $16K \le q$;
--   - for every $u \in S$, `Φ.periodicValue` $(x(u) - x_0) \ne 0$;
--   - for every $u \in S$ and every $i$, $\bigl| \sum_j M_{ij}\, x(u)_j - \beta(u)_i \bigr| \le 1/4$.
--
--   Then there is $c \in \mathbb{Z}^m$ such that for every $u \in S$,
--   $$\beta(u)_i = c_i + \sum_j M_{ij} \cdot \bigl(\texttt{Phi.integerLift}(x(u) - x_0)\bigr)_j \quad \text{for all } i.$$
--
--   Lean: `OAI.Erdos3.exists_torusCell_affine_recovery_s2`, which states OpenAI's `OAI.Erdos3.exists_torusCell_affine_recovery` (in `lean/OAI/Combinatorics/Progressions/Fourier/TorusCellBudget.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B100` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/TorusCellBudget.lean (declaration OAI.Erdos3.exists_torusCell_affine_recovery)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100

section

namespace OAI

section

namespace Erdos3

theorem exists_torusCell_affine_recovery_s2 {Ω : Type*} {d m q : ℕ}
    (hq : 8 ≤ q) (S : Set Ω) (M : Fin m → Fin d → ℤ) (a : Fin d → Fin q)
    (x : Ω → Fin d → ℝ) (β : Ω → Fin m → ℤ) {K : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hmesh : 16 * K ≤ (q : ℝ))
    (hactive : ∀ u ∈ S, (torusGridKernel d q hq a).periodicValue (x u - torusGridCenter q a) ≠ 0)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j *
      (torusGridKernel d q hq a).integerLift (x u - torusGridCenter q a) j := by
  sorry

end Erdos3

end

end OAI
end
