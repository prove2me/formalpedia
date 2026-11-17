-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_1_4
-- name    : NewtonLCP.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:18:00.449527+00:00
-- url     : https://prove2.me/theorems/51b473dd-ed89-4e0d-8059-2b1395f54f45
-- title:
--   Theorem 1.4 — approximating $1+4\hat\kappa(M)$ on upper triangular P-matrices yields an approximation of Max-Cut
-- statement:
--   Let $\alpha\ge1$ be a fixed real. If there is a polynomial-time multiplicative $\alpha$-approximation of
--
--   $$1+4\hat\kappa(M)$$
--
--   on the class of upper triangular rational P-matrices $M\in P\cap\mathbb Q^{n\times n}$, then there is a polynomial-time multiplicative $\alpha$-approximation of the Max-Cut value $\mathrm{maxcut}(G)$ on all finite simple graphs $G$.
--
--   The statement holds for both conventions of multiplicative approximation, $v/\alpha\le y\le v$ and $v\le y\le\alpha v$, each implying the same convention for Max-Cut. Combined with the known inapproximability of Max-Cut (a factor better than $17/16$ is NP-hard), it shows that the handicap number is hard to approximate even on upper triangular P-matrices.
--
--   **Formalization Note** Instances are encoded in binary (matrices by `encMat`, graphs by `encGraph`), and polynomial time is that of the published `CookPvsNP_defs`. The hypothesis algorithm is only required to be correct on upper triangular rational P-matrices; the conclusion is for every finite simple graph, connected or not, any number of vertices.
--
--   Differences from the source:
--   - reading: "multiplicative α-approximation" (direction not printed) → the implication stated for both conventions, $v/\alpha\le y\le v$ and $v\le y\le\alpha v$, as a conjunction, for every real $\alpha\ge1$; reason: the paper fixes neither convention; stating both is stronger than either reading alone, and the proof transfers each.
--   - reading: "α-approximation for Max-Cut" (p.4 states Max-Cut as finding a subset $S$) → approximation of the value $\mathrm{maxcut}(G)$ (the output is the code of a rational number, not a cut); reason: the hypothesis approximates a number ($1+4\hat\kappa(M)$), and the proof on p.28 transfers exactly that number ("yields the same approximation guarantee for the max cut of $G$", with $1+4\hat\kappa(M_G)=4\,\mathrm{maxcut}(G)$); no cut is produced.
--   - encoding: polynomial-time algorithms on matrices and graphs → polynomial-time computable maps on binary codes (`encMat`, `encGraph`, outputs `encQ y`) in the model of `CookPvsNP_defs`; reason: the paper names no encoding or machine model; the encodings are injective and of polynomial size.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.4, p.4 (proof §7.2, pp.26–28)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_PriceRobust_Stability_ZPMatrix
import Definitions.Def_NewtonLCP_Supplement_MaxCut

namespace NewtonLCP.Supplement

/-- **Theorem 1.4** (handicap approximation implies Max-Cut approximation). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.4, p.4
(proof §7.2, pp.26–28).

A polynomial-time multiplicative `α`-approximation for `1 + 4κ̂(M)`, restricted to upper
triangular matrices `M ∈ P ∩ ℚⁿˣⁿ`, implies a polynomial-time multiplicative `α`-approximation
for Max-Cut.

**Formalization Note.**
* Instances: rational square matrices `⟨n, M⟩` encoded by `encMat`; the hypothesis algorithm need
  only be correct on upper triangular (`M i j = 0` for `j < i`) matrices with
  `IsPMatrix (M.map ↑)` (the published `PriceRobust.Stability.IsPMatrix`), where the value is
  `1 + 4·handicap (M.map ↑)` (P-matrices are in `P⋆`, so this is the true `κ̂`). The conclusion is
  for **all** finite simple graphs `⟨n, G⟩` (any `n`, connected or not), encoded by `encGraph`,
  with value `maxcut G`.
* The approximation is of the value (the proof transfers a number). The direction of the
  estimate is not printed, so the implication is stated for both conventions, for every fixed real
  `α ≥ 1`: `v/α ≤ y ≤ v` (`IsLowerApprox`) and `v ≤ y ≤ α·v` (`IsUpperApprox`).
* Polynomial time is the published `CookPvsNP.PolyTimeComputable` over `Bool`. -/
theorem theorem_1_4 (α : ℝ) (hα : 1 ≤ α) :
    ((∃ f, IsLowerApprox (fun I : (Σ n : ℕ, Matrix (Fin n) (Fin n) ℚ) => encMat I.2)
        (fun I => (∀ i j, j < i → I.2 i j = 0) ∧
          PriceRobust.Stability.IsPMatrix (I.2.map ((↑) : ℚ → ℝ)))
        (fun I => 1 + 4 * handicap (I.2.map ((↑) : ℚ → ℝ))) α f) →
      ∃ g, IsLowerApprox (fun G : (Σ n : ℕ, SimpleGraph (Fin n)) => encGraph G.2)
        (fun _ => True) (fun G => (maxcut G.2 : ℝ)) α g) ∧
    ((∃ f, IsUpperApprox (fun I : (Σ n : ℕ, Matrix (Fin n) (Fin n) ℚ) => encMat I.2)
        (fun I => (∀ i j, j < i → I.2 i j = 0) ∧
          PriceRobust.Stability.IsPMatrix (I.2.map ((↑) : ℚ → ℝ)))
        (fun I => 1 + 4 * handicap (I.2.map ((↑) : ℚ → ℝ))) α f) →
      ∃ g, IsUpperApprox (fun G : (Σ n : ℕ, SimpleGraph (Fin n)) => encGraph G.2)
        (fun _ => True) (fun G => (maxcut G.2 : ℝ)) α g) := by sorry

end NewtonLCP.Supplement
