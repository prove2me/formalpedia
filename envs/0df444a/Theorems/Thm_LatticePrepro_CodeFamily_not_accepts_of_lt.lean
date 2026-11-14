-- Prove2me | Theorems.Thm_LatticePrepro_CodeFamily_not_accepts_of_lt
-- name    : LatticePrepro.CodeFamily.not_accepts_of_lt
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:15.924433+00:00
-- url     : https://prove2.me/theorems/80eb176a-2d61-40b5-b5bb-aff00dc93cbb
-- title:
--   Lemma 5.2 (codes, NO instances) — every vector is rejected
-- statement:
--   Let $F$ be a field and $(\mathcal C,(t_x)_{x\in X})$ a code family over $F$ with coordinate set $M$. Let $g,R\in\mathbb N$ and let $x$ be an instance with
--   $$\Delta(t_x,\mathcal C)>g\cdot R.$$
--   Then no vector $c\in F^M$ is accepted by the test with threshold $g\cdot R$: it is not the case that $c\in\mathcal C$ and $\Delta(t_x,c)\le g\cdot R$. Here $\Delta$ is the Hamming distance and $\Delta(t_x,\mathcal C)=\min_{c'\in\mathcal C}\Delta(t_x,c')$.
--
--   This is the NO half of Lemma 5.2 (Testing search outputs) for codes. In Theorem 5.1 for codes it is applied with $R=D$ and the gap $g$, using $\Delta(t_x,\mathcal C)>g\cdot D$ on NO instances (Lemma 3.11): whatever a search algorithm returns on a NO instance, the test rejects it.
--
--   **Formalization Note.** The NO condition is given directly as the bound on $\Delta(t_x,\mathcal C)$, a natural number (`codeDist`), and $c$ ranges over all of $F^M$, not only over codewords. The test is the predicate `CodeFamily.Accepts g R x c`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 5.2 (\label{lem:search-test}), codes, NO instances; Lean: LatticePrepro/Conversions/SearchTest.lean, LatticePrepro.CodeFamily.not_accepts_of_lt

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
open LatticePrepro.CodeFamily
variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

theorem LatticePrepro.CodeFamily.not_accepts_of_lt {g R : ℕ} {x : X} (hx : g * R < codeDist (C.target x) C.code)
    (c : C.M → F) : ¬ C.Accepts g R x c := by sorry
