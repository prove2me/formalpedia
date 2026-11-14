-- Prove2me | Theorems.Thm_LatticePrepro_LinearSystemFamily_code_no
-- name    : LatticePrepro.LinearSystemFamily.code_no
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:19.648287+00:00
-- url     : https://prove2.me/theorems/d3afa9e9-6ea5-48a5-aea5-78f95f618a26
-- title:
--   Lemma 3.11, eq. (38), NO instances — every codeword is far from the target
-- statement:
--   Let $p$ be a prime and $L$ a linear-system family over $\mathbb F_p$: a fixed linear map $A$ on $\mathbb F_p^{\iota}$, right-hand sides $b_x$, and a partition of the columns $\iota$ into $D$ blocks of size $Q$ each. Let $\mathcal C_L=\ker A\times\{0\}\subseteq\mathbb F_p^{\iota\sqcup\iota}$ and $y_x$ be its code and targets (`LinearSystemFamily.code`, `codeTarget`). Let $g$ be a natural number with $g<Q$, and assume $D>0$.
--
--   If $x$ is a NO instance with gap $g$, meaning that every solution $v\in\mathbb F_p^{\iota}$ of $Av=b_x$ has Hamming weight $\operatorname{wt}(v)>g\cdot D$, then
--   $$\Delta(y_x,c)>g\cdot D\qquad\text{for every codeword } c\in\mathcal C_L,$$
--   where $\Delta$ is the Hamming distance. Equivalently, $\Delta(y_x,\mathcal C_L)>g\cdot D$.
--
--   This is the NO half of the gap (38) in the proof of Lemma 3.11 (Appendix B.1). Together with the YES half it gives a $g$-gap NCPP instance with radius $D$, and it is the source of the NO bounds in the lattice reduction of Lemma 3.12.
--
--   **Formalization Note.** The gap is $\Gamma$ in the paper and $g$ in Lean; the block size $Q$ is `L.blockSize` and $D$ is `L.numBlocks`. The hypotheses $g<Q$ and $D>0$ are explicit here; in the paper they are part of Definition 3.10 ($Q>\Gamma$, $D\ge1$). The paper states the conclusion as a bound on $\Delta(y_x,\mathcal C_L)$; Lean states it for every codeword.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 3.11 (\label{lem:block-system-codes}), NO case of equation (38) (\label{eq:code-gap}) in its proof (Appendix B.1); Lean: LatticePrepro/Conversions/Codes.lean, LatticePrepro.LinearSystemFamily.code_no

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

theorem LatticePrepro.LinearSystemFamily.code_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.code, g * L.numBlocks < hammingDist (L.codeTarget x) c := by sorry
