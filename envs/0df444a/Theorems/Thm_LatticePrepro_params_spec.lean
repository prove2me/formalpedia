-- Prove2me | Theorems.Thm_LatticePrepro_params_spec
-- name    : LatticePrepro.params_spec
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:48:53.007472+00:00
-- url     : https://prove2.me/theorems/2965c9de-7fa4-4b70-92b6-9801151b1227
-- title:
--   Choice of the gap and size exponents for Theorem 5.1
-- statement:
--   Let $p$ be a natural number and $\delta$ a real number with $0\le\delta<1$. Set
--   $$m=\Bigl\lceil\frac{\delta}{1-\delta}\Bigr\rceil+1,\qquad a=(8p^4m+1)(m+7)m,\qquad k=\Bigl\lceil\frac{6m+a}{m-\delta(m+1)}\Bigr\rceil+1,\qquad C=a+k(m+1)+2.$$
--   These are $m=$ `momentAxes δ`, $a=$ `prefactorExp p m`, $k=$ `gapExp p δ` and $C=$ `sizeExp p δ`. Let $S\ge1$ and $n\ge1$ be integers with
--   $$n^m\le\bigl(8p^4m(S+1)\bigr)^{(m+7)m}\cdot\bigl((S+1)^k\bigr)^{m+1}.$$
--   Then
--   $$64\,n^{\delta}\le(S+1)^k\qquad\text{and}\qquad 4n\le(S+1)^C.$$
--
--   This is the parameter bookkeeping in the proof of Theorem 5.1. There, $n$ is the number of columns of the system given by Theorem 4.8 with $m$ moment axes and gap $g=(S+1)^k$, so the hypothesis is exactly the size bound of Theorem 4.8. The code or lattice dimension $M$ satisfies $M\le4n$, so the conclusions give the gap requirement $16M^\delta\le g$ (compare (25)) and the dimension bound $M\le(S+1)^C$. Here $k$ plays the role of the paper's exponent $K$, and the constants are explicit.
--
--   **Formalization Note** The ceilings are `Nat.ceil`. $n^\delta$ is a real power (`Real.rpow`), and $(S+1)^k$ is cast from $\mathbb{N}$ to $\mathbb{R}$ in the first conclusion. The lemma does not require $p$ to be prime.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847); auxiliary lemma used in the proof of Theorem 5.1 (\label{thm:approximation-hardness}), choice of parameters and inequality (25) (\label{eq:final-gap-requirement}); Lean: LatticePrepro/Main.lean, LatticePrepro.params_spec

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main

open LatticePrepro

theorem LatticePrepro.params_spec (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S n : ℕ) (hS : 1 ≤ S)
    (hn : 1 ≤ n)
    (hbound : n ^ momentAxes δ ≤ (8 * p ^ 4 * momentAxes δ * (S + 1)) ^
      ((momentAxes δ + 7) * momentAxes δ) * ((S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1)) :
    64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ gapExp p δ : ℕ) ∧ 4 * n ≤ (S + 1) ^ sizeExp p δ := by sorry
