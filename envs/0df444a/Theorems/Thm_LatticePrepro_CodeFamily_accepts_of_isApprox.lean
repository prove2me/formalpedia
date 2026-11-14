-- Prove2me | Theorems.Thm_LatticePrepro_CodeFamily_accepts_of_isApprox
-- name    : LatticePrepro.CodeFamily.accepts_of_isApprox
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:22.495709+00:00
-- url     : https://prove2.me/theorems/41320590-4c03-4d41-9422-cb1d95ec81a6
-- title:
--   Lemma 5.2 (codes, YES instances) — approximate solutions pass the test
-- statement:
--   Let $F$ be a field and $(\mathcal C,(t_x)_{x\in X})$ a code family over $F$: a linear code $\mathcal C\subseteq F^M$ and targets $t_x\in F^M$. Let $g,R\in\mathbb N$, let $x$ be an instance with
--   $$\Delta(t_x,\mathcal C)\le R,$$
--   and let $f$ be a real number with $f\le g$. If $c$ is an $f$-approximate solution for $x$, that is, $c\in\mathcal C$ and $\Delta(t_x,c)\le f\cdot\Delta(t_x,\mathcal C)$, then $c$ is accepted by the test with threshold $g\cdot R$:
--   $$c\in\mathcal C\qquad\text{and}\qquad\Delta(t_x,c)\le g\cdot R.$$
--   Here $\Delta$ is the Hamming distance and $\Delta(t_x,\mathcal C)=\min_{c'\in\mathcal C}\Delta(t_x,c')$ (Definition 3.1).
--
--   This is the YES half of Lemma 5.2 (Testing search outputs) for codes. In Theorem 5.1 for codes it is applied with the radius $R=D$ of Lemma 3.11, the gap $g$ and $f=M^{1-\varepsilon}\le g$: on a YES instance, every $M^{1-\varepsilon}$-approximate codeword passes the test.
--
--   **Formalization Note.** The statement is for an arbitrary code family over any field with decidable equality, with the YES condition given directly as the bound $\Delta(t_x,\mathcal C)\le R$. The paper's hypotheses $f\ge1$ and $\Gamma>16f$ (the case $s=1$) are replaced by the weaker $f\le g$, and the threshold $\Gamma\cdot D$ appears as $g\cdot R$. The test and approximate solutions are the predicates `CodeFamily.Accepts` and `CodeFamily.IsApprox`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 5.2 (\label{lem:search-test}), codes, YES instances; Lean: LatticePrepro/Conversions/SearchTest.lean, LatticePrepro.CodeFamily.accepts_of_isApprox

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

theorem LatticePrepro.CodeFamily.accepts_of_isApprox {g R : ℕ} {x : X} (hx : codeDist (C.target x) C.code ≤ R) {f : ℝ}
    (hfg : f ≤ g) {c : C.M → F} (hc : C.IsApprox f x c) : C.Accepts g R x c := by sorry
