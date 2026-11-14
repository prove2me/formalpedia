-- Prove2me | Theorems.Thm_LatticePrepro_LatticeReduction_not_accepts_of_isNo
-- name    : LatticePrepro.LatticeReduction.not_accepts_of_isNo
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:06.438437+00:00
-- url     : https://prove2.me/theorems/eb09d913-7958-450f-8b09-22f937917fc4
-- title:
--   Lemma 5.2 (lattices, NO instances) — every vector is rejected
-- statement:
--   Let $\mathsf p$ be a prime, $L$ a linear-system family over $\mathbb F_{\mathsf p}$ (fixed linear map $A$, right-hand sides $b_x$, $D$ blocks), $g\in\mathbb N$, $p$ a norm exponent, and let `Red` be a lattice reduction for $L$, $g$ and $p$ with lattice $\Lambda\subseteq\mathbb Z^M$ and residual weight $w$. If $x$ is a NO instance of $L$ with gap $g$, meaning that every solution of $Au=b_x$ has Hamming weight greater than $g\cdot D$, then no integer vector is accepted:
--   $$\neg\bigl(v\in\Lambda\ \text{ and }\ w(x,v)\le g\cdot D\bigr)\qquad\text{for every }v\in\mathbb Z^M.$$
--
--   This is the NO half of Lemma 5.2 (Testing search outputs) for lattices. Together with the YES half it shows that an approximate-CVPP search algorithm on these lattices, followed by the test, decides the underlying language; this is how the proof of Theorem 1.1 handles the search problem.
--
--   **Formalization Note.** The NO condition is `L.IsNo g x`, for the same gap $g$ as the reduction, and $v$ ranges over all of $\mathbb Z^M$. No condition on an approximation factor is needed. The test is the predicate `LatticeReduction.Accepts`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 5.2 (\label{lem:search-test}), lattices, NO instances; Lean: LatticePrepro/Conversions/SearchTest.lean, LatticePrepro.LatticeReduction.not_accepts_of_isNo

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

open LatticePrepro
open LatticePrepro.LatticeReduction
variable {p : ℕ} [Fact p.Prime] {X : Type} {L : LinearSystemFamily (ZMod p) X} {g : ℕ}
  {pn : PNorm} (Red : LatticeReduction L g pn)

theorem LatticePrepro.LatticeReduction.not_accepts_of_isNo {x : X} (hx : L.IsNo g x) (v : Red.Λ.M → ℤ) : ¬ Red.Accepts x v := by sorry
