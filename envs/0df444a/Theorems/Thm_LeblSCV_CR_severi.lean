-- Prove2me | Theorems.Thm_LeblSCV_CR_severi
-- name    : LeblSCV.CR.severi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:14:28.313084+00:00
-- url     : https://prove2.me/theorems/f6a60f10-2591-4311-acad-573abce7cc84
-- title:
--   Theorem 3.2.9 (Severi) — real-analytic CR functions extend holomorphically
-- statement:
--   Let $M \subset \mathbb{C}^n$ be a real-analytic hypersurface and $p \in M$. For every real-analytic CR function $f : M \to \mathbb{C}$ there exist an open neighborhood $U$ of $p$ and a holomorphic function $F \in \mathcal{O}(U)$ with
--   $$F(q) = f(q) \qquad \text{for all } q \in M \cap U.$$
--   So on a real-analytic hypersurface the tangential Cauchy–Riemann equations are the only obstruction to being locally the trace of a holomorphic function; the converse is Proposition 3.2.6. Example 3.2.7 shows that real-analyticity of $f$ cannot be dropped.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; $f$ is an ambient function of which only the values on $M$ matter. The hypothesis is `IsRealAnalyticCRFunction M f`: $f$ is real-analytic on $M$ (Definition 3.2.1) and satisfies the CR condition of Definition 3.2.3, stated intrinsically through $T^{(0,1)}_pM$, not as "restriction of a holomorphic function" (which is the conclusion). Holomorphic on the open set $U$ is `DifferentiableOn ℂ F U`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 115, Theorem 3.2.9

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticHypersurface
import Definitions.Def_LeblSCV_CR_IsSmoothCRFunction

namespace LeblSCV.CR

/-- Theorem 3.2.9 (Severi; Lebl, p. 115): if `M ⊂ ℂⁿ` is a real-analytic hypersurface and
`p ∈ M`, then for every real-analytic CR function `f : M → ℂ` there is a holomorphic function
`F ∈ 𝒪(U)` on an open neighbourhood `U` of `p` with `F q = f q` for all `q ∈ M ∩ U`. -/
theorem severi {n : ℕ} (M : Set (Fin n → ℂ)) (hM : IsRealAnalyticHypersurface M)
    (p : Fin n → ℂ) (hp : p ∈ M) (f : (Fin n → ℂ) → ℂ) (hf : IsRealAnalyticCRFunction M f) :
    ∃ (U : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ), IsOpen U ∧ p ∈ U ∧
      DifferentiableOn ℂ F U ∧ ∀ q ∈ M ∩ U, F q = f q := by sorry

end LeblSCV.CR
