-- Prove2me | Theorems.Thm_OAI_FiniteCircle_range_distortion_lower
-- name    : OAI.FiniteCircle.range_distortion_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:55:34.135445+00:00
-- url     : https://prove2.me/theorems/32aaf7c6-d7c9-49d5-aa70-da9d066779ab
-- title:
--   Fourier-analytic lower bound for the $\ell_1$ distortion of a word family indexed by $(\mathbb Z_M)^I$
-- statement:
--   **Notation.** Let $I$ be a finite set, $M\ge1$, $\mathbb Z_M=\mathbb Z/M\mathbb Z$ and $G=(\mathbb Z_M)^I$, with unit vectors $e_i$ ($i\in I$). For $\xi\in\mathbb Z_M$ let $|\xi|_M=\min(\bar\xi,M-\bar\xi)$, where $\bar\xi\in\{0,\dots,M-1\}$ represents $\xi$, be its distance to $0$ on the cycle. A *character* of $G$ is a homomorphism $\chi$ from $(G,+)$ to the multiplicative group of $\mathbb C$; its *coordinate frequencies* are the unique $\xi_i(\chi)\in\mathbb Z_M$ with $\chi(a e_i)=e^{2\pi \mathrm i\,\xi_i(\chi)a/M}$ for all $a\in\mathbb Z_M$. For words over an alphabet $\alpha$, $\operatorname{ed}$ is the edit distance (least number of single-letter insertions, deletions and substitutions). For a set $S$ of words, its optimal $\ell_1$ distortion $c_1(S)$ is the infimum, over all injective maps $f\colon S\to\ell_1(\mathbb N)$, of
--   $$\Bigl(\sup_{x\neq y}\frac{\|f(x)-f(y)\|_1}{\operatorname{ed}(x,y)}\Bigr)\cdot\Bigl(\sup_{x\neq y}\frac{\operatorname{ed}(x,y)}{\|f(x)-f(y)\|_1}\Bigr).$$
--
--   **Hypotheses.** Let $H\le G$ be a subgroup, $w\in G$ and $B>0$, and assume the *frequency condition*: every character $\chi$ of $G$ that is trivial on $H$ and satisfies $\chi(w)\neq1$ has $\sum_{i\in I}|\xi_i(\chi)|_M\ge B$. Let $W\colon G\to\alpha^*$ be any map into words, and let $h,R,L,\kappa,u,\delta,D$ be real numbers with $L>0$, $\delta>0$ and $L=M\,|I|\,\kappa$. Put $J=\lfloor\log_2 M\rfloor+1$ and assume, for all $v\in G$:
--
--   1. (cheap directions) $\operatorname{ed}(W(v),W(v+c))\le 2uhL/R$ for every $c\in H$;
--   2. (dyadic coordinate shifts) $\operatorname{ed}(W(v),W(v+2^j e_i))\le 2u\kappa\,2^j$ for every $i\in I$ and $0\le j<J$;
--   3. (long direction) $\delta L\le\operatorname{ed}(W(v),W(v+w))$;
--   4. (numerics) every real $t\ge 0$ with $\delta\le t\,u\,\bigl(4h/R+2J/B\bigr)$ satisfies $D\le t$.
--
--   **Conclusion.** The set of words $W(G)=\{W(v):v\in G\}$ satisfies
--
--   $$
--   D\;\le\;c_1\bigl(W(G)\bigr).
--   $$
--
--   This is the analytic engine of the lower bound: a family of words that moves little under translations by $H$ and under dyadic coordinate shifts, but moves a lot under translation by $w$, cannot be embedded into $\ell_1$ with small distortion. The frequency condition expresses that $w$ is far, in the Fourier sense, from $H$ and from the coordinate directions; hypothesis 4 packages the final arithmetic so that the theorem can be applied with any explicit target value $D$.
--
--   **Formalization Note** The parameter $\kappa$ is the variable `copies`; the dyadic shift is `Pi.single i ((2^j : ℕ) : ZMod M)` with `j : Fin (Nat.log 2 M+1)`; the coordinate frequency is `coordinateFrequency χ i` and $|\xi|_M$ is `ξ.valMinAbs.natAbs`; "trivial on $H$" is `χ.compAddMonoidHom H.subtype = 0`, where the zero of `AddChar` is the trivial character. No sign conditions are imposed on $h$, $R$, $u$, and division by $R=0$ follows Lean's convention $x/0=0$. The conclusion is about `optimalDistortion` of the inclusion of `Set.range W` into the words over $\alpha$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Distortion.lean#L232-L267

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem OAI.FiniteCircle.range_distortion_lower {I α : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} [NeZero M] (H : AddSubgroup (I → ZMod M)) [Fintype H]
    (w : I → ZMod M) (B : ℝ) (hB : 0<B)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ w≠1 →
      B ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (h R L copies u δ D : ℝ) (hL : 0<L) (hδ : 0<δ)
    (hcL : L=(M:ℝ)*Fintype.card I*copies)
    (hcheap : ∀ v (c : H), (editDistance (W v) (W (v+c)):ℝ) ≤ u*2*h*L/R)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      (editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))):ℝ) ≤ u*2*copies*(2:ℝ)^j.val)
    (hlong : ∀ v, δ*L ≤ (editDistance (W v) (W (v+w)):ℝ))
    (hnum : ∀ t : ℝ, 0≤t → δ ≤ t*u*(4*h/R+2*(Nat.log 2 M+1:ℕ)/B) → D≤t) :
    D ≤ optimalDistortion (fun x : Set.range W => x.val) := by sorry
