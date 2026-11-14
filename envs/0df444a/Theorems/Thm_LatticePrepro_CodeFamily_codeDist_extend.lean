-- Prove2me | Theorems.Thm_LatticePrepro_CodeFamily_codeDist_extend
-- name    : LatticePrepro.CodeFamily.codeDist_extend
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:25:08.753892+00:00
-- url     : https://prove2.me/theorems/e01fa1f5-c08f-4a46-99bc-150d67f365c2
-- title:
--   Lemma 3.11 (extension of scalars) — distances to a code over $\mathbb F_p$ are preserved over larger fields
-- statement:
--   Let $p$ be a prime and $F$ a field with an $\mathbb F_p$-algebra structure (so $F$ has characteristic $p$ and contains $\mathbb F_p$), with decidable equality. Let $(\mathcal C,(t_x)_{x\in X})$ be a code family over $\mathbb F_p$ with coordinate set $M$, and let $\mathcal C_F=\operatorname{span}_F\mathcal C\subseteq F^M$ be its extension to $F$, with the targets $t_x$ read in $F^M$ via $\mathbb F_p\hookrightarrow F$ (`CodeFamily.extend F`). Then for every instance $x\in X$,
--   $$\Delta(t_x,\mathcal C_F)=\Delta(t_x,\mathcal C),$$
--   where $\Delta(y,\mathcal C)=\min_{c\in\mathcal C}\Delta(y,c)$ is the Hamming distance from a word to a code (Definition 3.1).
--
--   This is the last step of the proof of Lemma 3.11 (Appendix B.1): the gap for the code $\ker A\times\{0\}$ over $\mathbb F_p$ transfers to the code it spans over any field of characteristic $p$. This is how Theorem 5.1 for codes covers every finite field.
--
--   **Formalization Note.** Both distances are `codeDist`, a natural number. The Lean statement does not require $F$ to be finite (the paper fixes a finite field); it only assumes `[Algebra (ZMod p) F]` and `[DecidableEq F]`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma 3.11 (\label{lem:block-system-codes}), extension-of-scalars step of its proof (Appendix B.1); Lean: LatticePrepro/Conversions/Codes.lean, LatticePrepro.CodeFamily.codeDist_extend

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes

open LatticePrepro
variable {p : ℕ} [Fact p.Prime] {X : Type} (F : Type) [Field F] [Algebra (ZMod p) F]

theorem LatticePrepro.CodeFamily.codeDist_extend [DecidableEq F] (C : CodeFamily (ZMod p) X) (x : X) :
    CodeFamily.codeDist ((C.extend F).target x) (C.extend F).code =
      CodeFamily.codeDist (C.target x) C.code := by sorry
