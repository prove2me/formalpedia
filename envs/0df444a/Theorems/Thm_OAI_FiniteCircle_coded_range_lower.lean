-- Prove2me | Theorems.Thm_OAI_FiniteCircle_coded_range_lower
-- name    : OAI.FiniteCircle.coded_range_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:01:56.945894+00:00
-- url     : https://prove2.me/theorems/d0938a65-c577-4cca-a21b-86f10846785a
-- title:
--   A binary-encoded word family indexed by $(\mathbb Z_M)^I$ has $\ell_1$ distortion at least $n^k$
-- statement:
--   **Notation.** For words $x,y$ over an alphabet, $\operatorname{ed}(x,y)$ is the edit distance (least number of single-letter insertions, deletions and substitutions), $\operatorname{lcs}(x,y)$ the length of a longest common subsequence, and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$ the *deficit*. For a finite alphabet $\alpha$ and a binary code $c\colon\alpha\to\{0,1\}^w$ of block length $w$, the encoding of a word is the concatenation of codewords, $\operatorname{enc}_c(x_1x_2\cdots x_m)=c(x_1)c(x_2)\cdots c(x_m)$. The code satisfies the *substitution bounds* with constants $a,C$ if (i) $w>0$; (ii) $w\le C\ln(2|\alpha|)$; (iii) for every $m$ and all $x,y\in\alpha^m$, $a\,w\operatorname{def}(x,y)\le\operatorname{def}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{def}(x,y)$; (iv) $\operatorname{ed}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{ed}(x,y)$ for all words $x,y$. For a set $S$ of words, $c_1(S)$ is its optimal $\ell_1$ distortion: the infimum over injective $f\colon S\to\ell_1(\mathbb N)$ of $\bigl(\sup_{x\neq y}\|f(x)-f(y)\|_1/\operatorname{ed}(x,y)\bigr)\cdot\bigl(\sup_{x\neq y}\operatorname{ed}(x,y)/\|f(x)-f(y)\|_1\bigr)$.
--
--   Let $I$ be a finite set, $M\ge1$, $\mathbb Z_M=\mathbb Z/M\mathbb Z$, $G=(\mathbb Z_M)^I$ with unit vectors $e_i$. For $\xi\in\mathbb Z_M$, $|\xi|_M$ is its distance to $0$ on the cycle. For a character $\chi$ of $G$ (a homomorphism into the multiplicative group of $\mathbb C$), its coordinate frequencies $\xi_i(\chi)\in\mathbb Z_M$ are defined by $\chi(ae_i)=e^{2\pi\mathrm i\,\xi_i(\chi)a/M}$ for $a\in\mathbb Z_M$.
--
--   **Hypotheses.** Let $n,k$ be natural numbers with $n\ge 10^6$ and $n^4=4k$, and suppose $\lfloor\log_2M\rfloor+1\le n^{13}$. Let $H\le G$ be a subgroup and $\theta\in G$ such that every character $\chi$ of $G$ that is trivial on $H$ and satisfies $\chi(\theta)\neq1$ has $\sum_{i\in I}|\xi_i(\chi)|_M\ge (n^4/2)^{n^4}$. Let $\alpha$ be a finite alphabet, $W\colon G\to\alpha^*$ a map into words, and $L,\kappa\in\mathbb N$ with $L>0$ and $L=M\,|I|\,\kappa$, such that for all $v\in G$:
--
--   1. $|W(v)|=L$;
--   2. $(n^4)^{2n^4}\operatorname{ed}(W(v),W(v+c))\le 2n^4L$ for every $c\in H$;
--   3. $\operatorname{ed}(W(v),W(v+2^je_i))\le 2\kappa\,2^j$ for every $i\in I$ and $0\le j\le\lfloor\log_2 M\rfloor$;
--   4. $L/n^{3n^4}\le\operatorname{def}(W(v),W(v+\theta))$.
--
--   Finally let $c\colon\alpha\to\{0,1\}^w$ satisfy the substitution bounds with $a=2^{-28}$ and $C=67108928$.
--
--   **Conclusion.**
--
--   $$
--   n^k\;\le\;c_1\Bigl(\bigl\{\operatorname{enc}_c(W(v)) : v\in G\bigr\}\Bigr).
--   $$
--
--   This transfers the Fourier-analytic distortion lower bound from words over a large alphabet to binary words: the substitution bounds guarantee that encoding multiplies all relevant edit distances and deficits by roughly the block length $w$, up to the fixed factor $2^{-28}$. Since $k=n^4/4$, the conclusion is a lower bound $n^{n^4/4}$; both explicit witness families of the main theorem (the mask words and the excluded-residue words) are run through this statement.
--
--   **Formalization Note** $\kappa$ is the variable `copies`; the dyadic shift is `Pi.single i ((2^j : ℕ) : ZMod M)` with `j : Fin (Nat.log 2 M+1)`; $\ln$ is `Real.log`; hypotheses 2 and 3 are inequalities in $\mathbb N$ and hypothesis 4 is in $\mathbb R$. "Trivial on $H$" is `χ.compAddMonoidHom H.subtype = 0`, the zero of `AddChar` being the trivial character. The conclusion is about `optimalDistortion` of the inclusion of `Set.range (fun v => encode c (W v))` into binary words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BinaryDistortion.lean#L11-L57

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

theorem OAI.FiniteCircle.coded_range_lower {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    {n k M : ℕ} [NeZero M] (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13)
    (H : AddSubgroup (I → ZMod M)) [Fintype H] (θ : I → ZMod M)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ θ≠1 →
      (((n^4:ℕ):ℝ)/2)^(n^4) ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (L copies : ℕ) (hL : 0<L)
    (hcL : L=M*Fintype.card I*copies) (hLen : ∀ v, (W v).length=L)
    (hcheap : ∀ v (c : H), (n^4)^(2*n^4)*editDistance (W v) (W (v+c)) ≤ 2*n^4*L)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))) ≤ 2*copies*2^j.val)
    (hlong : ∀ v, (L:ℝ)/(n:ℝ)^(3*n^4) ≤ (deficit (W v) (W (v+θ)):ℝ))
    {w : ℕ} (c : α → Fin w → Bool) (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ optimalDistortion (fun x : Set.range (fun v => encode c (W v)) => x.val) := by sorry
