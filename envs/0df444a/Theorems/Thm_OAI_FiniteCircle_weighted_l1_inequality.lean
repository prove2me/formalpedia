-- Prove2me | Theorems.Thm_OAI_FiniteCircle_weighted_l1_inequality
-- name    : OAI.FiniteCircle.weighted_l1_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:48:36.918614+00:00
-- url     : https://prove2.me/theorems/e52930bf-7ab0-4f61-9e54-ae112f37e6ae
-- title:
--   Weighted $\ell^1$ displacement inequality from an annihilator frequency bound and dyadic coordinate shifts
-- statement:
--   Let $I$ be a finite set, $M\ge1$, $V=(\mathbb{Z}/M)^I$, $H\le V$ a subgroup, $w\in V$ and $B>0$. Every additive character $\chi$ of $V$ (a homomorphism into the multiplicative group of $\mathbb{C}$) is determined by its frequencies $\xi_i(\chi)\in\mathbb{Z}/M$, $i\in I$, defined by $\chi(a\,e_i)=e^{2\pi\mathrm{i}\,\xi_i(\chi)a/M}$ for all $a\in\mathbb{Z}/M$, where $e_i$ is the $i$-th standard basis vector. For $y\in\mathbb{Z}/M$ let $|y|_M\in\{0,\dots,\lfloor M/2\rfloor\}$ be the absolute value of its representative in $(-M/2,M/2]$. Let $\ell^1$ be the space of absolutely summable real sequences with norm $\|\cdot\|_1$, and let $\mathbb{E}$ denote uniform averages.
--
--   Assume that every character $\chi$ of $V$ that is trivial on $H$ and satisfies $\chi(w)\ne1$ has $\sum_{i\in I}|\xi_i(\chi)|_M\ge B$. Then every map $f:V\to\ell^1$ satisfies
--
--   $$
--   \mathbb{E}_{v\in V}\|f(v+w)-f(v)\|_1\le2\,\mathbb{E}_{c\in H}\,\mathbb{E}_{v\in V}\|f(v+c)-f(v)\|_1+\frac1B\sum_{i\in I}\sum_{j=0}^{\lfloor\log_2M\rfloor}\frac{M}{2^j}\,\mathbb{E}_{v\in V}\big\|f(v+2^je_i)-f(v)\big\|_1 .
--   $$
--
--   In the edit-distance lower bound, $V$ indexes a family of words, the shifts in $H$ are cheap (they change words little), and the dyadic single-coordinate shifts $2^je_i$ move words by a controlled amount; the inequality then forces every $\ell^1$ embedding to contract the long shift $w$ unless it has large distortion.
--
--   **Formalization Note** $\xi_i(\chi)$ is `coordinateFrequency χ i`, $|y|_M$ is `(y.valMinAbs).natAbs`, $\lfloor\log_2M\rfloor$ is `Nat.log 2 M`, $2^je_i$ is `Pi.single i ((2^j : ℕ) : ZMod M)`, and "trivial on $H$" is `χ.compAddMonoidHom H.subtype = 0` (in Mathlib the zero character is the trivial one).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/DyadicShifts.lean#L203-L239

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.weighted_l1_inequality {I : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0 < B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ,
      χ.compAddMonoidHom H.subtype = 0 → χ w ≠ 1 →
        B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (f : (I → ZMod M) → RealL1) :
    (𝔼 v, ‖f (v+w)-f v‖) ≤
      2*(𝔼 c : H, 𝔼 v, ‖f (v+c)-f v‖) + (1/B)*
      ∑ i, ∑ j : Fin (Nat.log 2 M+1), (M:ℝ)/(2:ℝ)^j.val *
        (𝔼 v, ‖f (v+Pi.single i ((2^j.val : ℕ):ZMod M))-f v‖) := by sorry
