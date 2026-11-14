-- Prove2me | Theorems.Thm_LatticePrepro_LinearSystemFamily_code_yes
-- name    : LatticePrepro.LinearSystemFamily.code_yes
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:00.268368+00:00
-- url     : https://prove2.me/theorems/150a9bb2-a70d-4c4a-9f36-660a79b3c68d
-- title:
--   Lemma 3.11, eq. (38), YES instances — a binary block-sparse error vector of weight at most $D$
-- statement:
--   Let $p$ be a prime and $L$ a linear-system family over $\mathbb F_p$ with instance set $X$: a fixed linear map $A$ on $\mathbb F_p^{\iota}$ ($\iota$ a finite set of columns), right-hand sides $b_x$, and a partition of $\iota$ into $D$ blocks. Let $\mathcal C_L=\ker A\times\{0\}\subseteq\mathbb F_p^{\iota\sqcup\iota}$ be its code and $y_x$ its targets, and give $\iota\sqcup\iota$ the block partition with a copy of the column blocks on each half (`LinearSystemFamily.code`, `codeTarget`, `codeBlk`).
--
--   Let $x$ be a YES instance of the block-sparse linear-system problem: $Av=b_x$ has a solution $v\in\{0,1\}^{\iota}$ with at most one nonzero coordinate in each block. Then there is $e\in\mathbb F_p^{\iota\sqcup\iota}$ such that
--   $$e\in\{0,1\}^{\iota\sqcup\iota},\qquad \operatorname{wt}(e)\le D,\qquad y_x-e\in\mathcal C_L,$$
--   and $e$ has at most one nonzero coordinate in each block of $\iota\sqcup\iota$. Here $\operatorname{wt}(e)$ is the Hamming weight, the number of nonzero coordinates.
--
--   This is the YES half of the gap (38) in the proof of Lemma 3.11 (Appendix B.1), together with the paper's remark that $e$ can be chosen with at most one nonzero entry per block. It shows $\Delta(y_x,\mathcal C_L)\le D$, so the code reduction has radius $R=D$; the block sparsity of $e$ is what the Hadamard step of the lattice reduction (Lemma B.2, Lemma 3.12) needs.
--
--   **Formalization Note.** "Binary" is `IsBinary` (every coordinate is $0$ or $1$ in $\mathbb F_p$), block sparsity is `AtMostOnePerBlock L.codeBlk`, the weight is Mathlib's `hammingNorm`, and $D$ is `L.numBlocks`, the number of block indices. YES instances are `L.IsYes x`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 3.11 (\label{lem:block-system-codes}), YES case of equation (38) (\label{eq:code-gap}) in its proof (Appendix B.1); Lean: LatticePrepro/Conversions/Codes.lean, LatticePrepro.LinearSystemFamily.code_yes

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LatticePrepro.LinearSystemFamily.code_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.ι ⊕ L.ι → ZMod p, IsBinary e ∧ AtMostOnePerBlock L.codeBlk e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.codeTarget x - e ∈ L.code := by sorry
