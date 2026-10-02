-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_hartogs_pseudoconvex_tfae
-- name    : LeblSCV.Pseudoconvex.hartogs_pseudoconvex_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:48:47.85879+00:00
-- url     : https://prove2.me/theorems/0f0c8f07-0d1b-4916-887d-8f903e477214
-- title:
--   Theorem 2.5.6 — characterizations of Hartogs pseudoconvexity
-- statement:
--   Let $U \subsetneq \mathbb{C}^n$ be a domain, and let $\rho(z)$ be the Euclidean distance from $z$ to $\partial U$. The following are equivalent:
--
--   (i) $-\log \rho(z)$ is plurisubharmonic on $U$;
--
--   (ii) $U$ is Hartogs pseudoconvex;
--
--   (iii) $U$ is convex with respect to the plurisubharmonic functions defined on $U$;
--
--   (iv) the conclusion of the Kontinuitätssatz (second version) holds: for any collection of closed analytic discs $\Delta_\alpha \subset U$,
--   $$\bigcup_\alpha \partial\Delta_\alpha \subset\subset U \implies \bigcup_\alpha \Delta_\alpha \subset\subset U.$$
--
--   The theorem reduces pseudoconvexity, a property that asks for a global function, to a condition on a single function of the domain's geometry ($-\log\rho$), and equally to the behaviour of families of analytic discs.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. $\rho(z)$ is `Metric.infDist z (frontier U)`, which is Euclidean on this space. It is positive on $U$ because $U \neq \mathbb{C}^n$ is open and $\partial U$ is nonempty and closed. A domain is `IsOpen U ∧ IsConnected U`, and $U \subsetneq \mathbb{C}^n$ is `U ≠ Set.univ`. The four conditions are `IsPlurisubharmonicOn`, `IsHartogsPseudoconvex`, `IsConvexWrt` and `SatisfiesContinuityPrinciple` of this mission, combined in `List.TFAE`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 92, Theorem 2.5.6

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_IsHartogsPseudoconvex
import Definitions.Def_LeblSCV_Pseudoconvex_IsConvexWrt
import Definitions.Def_LeblSCV_Pseudoconvex_SatisfiesContinuityPrinciple

namespace LeblSCV.Pseudoconvex

/-- Theorem 2.5.6 (Lebl, p. 92). Let `U ⊊ ℂⁿ` be a domain (connected open set, `U ≠ ℂⁿ`).
The following are equivalent:
(i) `−log ρ(z)` is plurisubharmonic on `U`, where `ρ(z)` is the Euclidean distance from `z`
to `∂U` (`Metric.infDist z (frontier U)` on `EuclideanSpace ℂ (Fin n)`);
(ii) `U` is Hartogs pseudoconvex;
(iii) `U` is convex with respect to plurisubharmonic functions defined on `U`;
(iv) the conclusion of the Kontinuitätssatz (second version) holds for `U`. -/
theorem hartogs_pseudoconvex_tfae {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hne : U ≠ Set.univ) :
    List.TFAE
      [IsPlurisubharmonicOn (fun z => ((-Real.log (Metric.infDist z (frontier U)) : ℝ) : EReal)) U,
       IsHartogsPseudoconvex U,
       IsConvexWrt U {f | IsPlurisubharmonicOn f U},
       SatisfiesContinuityPrinciple U] := by sorry

end LeblSCV.Pseudoconvex
