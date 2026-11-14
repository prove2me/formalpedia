-- Prove2me | Theorems.Thm_LatticePrepro_ExplicitTables_soundness_setup
-- name    : LatticePrepro.ExplicitTables.soundness_setup
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:20.770433+00:00
-- url     : https://prove2.me/theorems/2076c34e-ebae-4a62-82c9-32e5585b6ef1
-- title:
--   Soundness setup — a light constrained table has a short dependence among its Hankel columns
-- statement:
--   Fix a field setup: a sample field $\mathbb{S}$ with $q$ elements and an extension $K=\mathbb{S}(\gamma)$ of degree $\delta$, of characteristic $p$. Let $m\ge1$ and $B\ge2$ be integers, let $\Delta=2pm(B-1)(\delta-1)$, assume $4\Delta<q$, and let $\ell=p(B^m-1)+1$. Let $y\in\mathbb{F}_p^{\,\mathbb{S}^m\times\mathbb{S}}$ be an evaluation table that satisfies all the constraints of Construction A.4 (low-degree, index-consistency and Frobenius) and has weight
--   $$2\,\mathrm{wt}(y)<B^m\cdot q .$$
--   Then there is a natural number $t$ with
--   $$t<B^m,\qquad q\cdot t\le2\,\mathrm{wt}(y),$$
--   and there are $c_0,\dots,c_t\in K$, not all zero, with
--   $$\sum_{j=0}^{t}c_j\,\hat\mu_{i+j}(y)=0\qquad(0\le i<\ell).$$
--   That is, the first $t+1$ columns of the $\ell\times\ell$ Hankel matrix $(\hat\mu_{i+j}(y))_{0\le i,j<\ell}$ of the moments of $y$ are linearly dependent over $K$.
--
--   This packages Lemma A.6 with the counting in the soundness part of the proof of Theorem A.8, where $t$ is the rank of the moment Hankel matrix and the paper shows $t\le4\,\mathrm{wt}(y)/(3q)<2r/3$ for $r=B^m$. Its conclusion is the hypothesis of the Hankel reconstruction Theorem A.7, which then yields a coefficient function with at most $t\le2\,\mathrm{wt}(y)/q$ support points.
--
--   **Formalization Note**: "Satisfies all the constraints" is `constraintFun FS m B y = 0`, and $\mathrm{wt}(y)$ is Mathlib's `hammingNorm` (the number of nonzero entries). The hypothesis $4\Delta<q$ is implied by the paper's choice $q\ge8pmB\delta$. The weight condition $2\,\mathrm{wt}(y)<B^m q$ is the soundness threshold $\mathrm{wt}(y)<rD/2$ of Definition 4.4 with $r=B^m$ and $D=q$ blocks.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847); auxiliary lemma used in the proof of Theorem A.8 (\label{thm:moment-representation-construction}), combining Lemma A.6 (\label{lem:table-rank}); Lean: LatticePrepro/Tables/TableSoundness.lean, LatticePrepro.ExplicitTables.soundness_setup

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_TableSoundness

open LatticePrepro
open Polynomial Matrix
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}

theorem LatticePrepro.ExplicitTables.soundness_setup (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ t : ℕ, t < B ^ m ∧ Fintype.card FS.𝕊 * t ≤ 2 * hammingNorm y ∧
      ∃ c : Fin (t + 1) → FS.K, c ≠ 0 ∧
        ∀ i : Fin (hLen p m B), ∑ j, c j * mom FS m B y (i.val + j.val) = 0 := by sorry
