-- Prove2me | Theorems.Thm_LatticePrepro_LatticeReduction_accepts_of_isApprox
-- name    : LatticePrepro.LatticeReduction.accepts_of_isApprox
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:16.877611+00:00
-- url     : https://prove2.me/theorems/3c8c5ede-4a93-40d7-878c-fcece9f10ce5
-- title:
--   Lemma 5.2 (lattices, YES instances) — approximate solutions pass the test
-- statement:
--   Let $\mathsf p$ be a prime, $L$ a linear-system family over $\mathbb F_{\mathsf p}$ with $D$ blocks, $g\in\mathbb N$, and $p$ a norm exponent (a real $p\ge1$ or $p=\infty$) with $s=\min\{p,2\}$. Let `Red` be a lattice reduction for $L$, $g$ and $p$ (the output of Lemma 3.12): a lattice $\Lambda\subseteq\mathbb Z^M$, targets $t_x$, a radius $R\ge1$ and a residual weight $w$. Let $f\ge0$ be a real number with
--   $$16\cdot f^{s}\le g.$$
--   If $x$ is a YES instance of $L$ and $v$ is an $f$-approximate solution, that is, $v\in\Lambda$ and $\|t_x-v\|_p\le f\cdot\operatorname{dist}_p(t_x,\Lambda)$, then $v$ is accepted:
--   $$v\in\Lambda\qquad\text{and}\qquad w(x,v)\le g\cdot D.$$
--   Here $\operatorname{dist}_p(t_x,\Lambda)=\min_{u\in\Lambda}\|t_x-u\|_p$ (Definition 3.1).
--
--   This is the YES half of Lemma 5.2 (Testing search outputs) for lattices. In Theorem 5.1 for lattices it is applied with $f=M^{1/s-\varepsilon}$, so that every $M^{1/s-\varepsilon}$-approximate solution to a YES instance passes the test.
--
--   **Formalization Note.** `Red : LatticeReduction L g pn` is an arbitrary lattice reduction; its YES radius bound and weight bound $w\le16D(\|t_x-v\|_p/R)^s$ are fields of the structure. The paper assumes $f\ge1$ and $\Gamma>16f^s$; Lean needs only $f\ge0$ and $16f^s\le g$, with $f^s$ a real power. $\operatorname{dist}_p(t_x,\Lambda)$ is `latticeDist`, and the test is the predicate `LatticeReduction.Accepts`. The polynomial running time of the test is not formalized.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 5.2 (\label{lem:search-test}), lattices, YES instances; Lean: LatticePrepro/Conversions/SearchTest.lean, LatticePrepro.LatticeReduction.accepts_of_isApprox

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

theorem LatticePrepro.LatticeReduction.accepts_of_isApprox {f : ℝ} (hf : 0 ≤ f) (hgf : 16 * f ^ pn.s ≤ g) {x : X}
    (hx : L.IsYes x) {v : Red.Λ.M → ℤ} (hv : Red.IsApprox f x v) : Red.Accepts x v := by sorry
