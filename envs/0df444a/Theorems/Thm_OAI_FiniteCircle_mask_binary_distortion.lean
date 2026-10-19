-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_binary_distortion
-- name    : OAI.FiniteCircle.mask_binary_distortion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:02:37.316611+00:00
-- url     : https://prove2.me/theorems/79d53356-57ec-4d41-aa56-b5089d8d18dc
-- title:
--   Binary-encoded mask words have $\ell_1$ distortion at least $n^{k}$ where $n^4=4k$
-- statement:
--   Let $n\ge10^6$ and $k$ be natural numbers with $n^4=4k$, and put $h=n^4$.
--
--   **Prime array.** Let $p\colon\mathbb N\times\mathbb N\to\mathbb N$, $(l,s)\mapsto p_{l,s}$, be a standing prime array for $h$: for $1\le l\le h$ and $0\le s<h$ the numbers $p_{l,s}$ are primes with $h^3<p_{l,s}\le2h^3$, these $h^2$ primes are pairwise distinct, and $p_{l,s}=1$ for all other pairs $(l,s)$. Put $P_l=\prod_{s<h}p_{l,s}$, $N=2\prod_{l=1}^hP_l$, $R=h^{2h}$ and $\mathbb Z_N=\mathbb Z/N\mathbb Z$.
--
--   **Mask words.** For $l\ge1$ let $T_l=\{(s,b):0\le s<h,\ 0\le b<p_{l,s}\}$, listed lexicographically. The alphabets are $\mathcal A_0=\{0,1\}$ and $\mathcal A_l=T_l\times\mathcal A_{l-1}$; the states are $\mathcal S_0=\mathbb Z_N$ and $\mathcal S_l=(\mathcal S_{l-1})^{T_l}$, so a state assigns an element of $\mathbb Z_N$ to every path $(j_l,\dots,j_1)$ with $j_r\in T_r$, and $v+\vartheta$ ($\vartheta\in\mathbb Z_N$) adds $\vartheta$ to all these entries. For $a\in\mathbb N$ and $j=(s',b)\in T_l$ define the phase
--   $$\gamma_l(a,j)=\sum_{s<h}\frac{N}{p_{l,s}}\,(a\bmod p_{l,s})+b\,\frac{N}{p_{l,s'}}\,(a\bmod p_{l,s'})\in\mathbb Z_N .$$
--   The mask word $\mathrm{mw}_0(v)$ of $v\in\mathbb Z_N$ is the binary word of length $N$ whose $b$-th letter ($0\le b<N$) is $1$ exactly when the residue of $b-v$ in $\{0,\dots,N-1\}$ is less than $N/2$, and for $l\ge1$ the word $\mathrm{mw}_l(v)$ is the concatenation, over $a=0,1,\dots,RP_l-1$ and, for each $a$, over $j\in T_l$ in the listed order, of the words $j\otimes\mathrm{mw}_{l-1}\bigl(v(j)+\gamma_l(a,j)\bigr)$, where $j\otimes x$ replaces every letter $y$ of $x$ by the pair $(j,y)$.
--
--   **Code.** Let $c\colon\mathcal A_h\to\{0,1\}^w$ be a binary code satisfying the substitution bounds with constants $a=2^{-28}$ and $C=67108928$: $w>0$; $w\le C\ln(2|\mathcal A_h|)$; $a\,w\operatorname{def}(x,y)\le\operatorname{def}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{def}(x,y)$ for all words $x,y$ of equal length; and $\operatorname{ed}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{ed}(x,y)$ for all words. Here $\operatorname{enc}_c$ concatenates the codewords of the letters, $\operatorname{ed}$ is edit distance and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$, with $\operatorname{lcs}$ the length of a longest common subsequence.
--
--   **Statement.**
--
--   $$
--   n^k\;\le\;c_1\Bigl(\bigl\{\operatorname{enc}_c(\mathrm{mw}_h(v)) : v\in\mathcal S_h\bigr\}\Bigr),
--   $$
--
--   where for a set $S$ of binary words $c_1(S)$ is the infimum, over injective maps $f\colon S\to\ell_1(\mathbb N)$, of $\bigl(\sup_{x\neq y}\|f(x)-f(y)\|_1/\operatorname{ed}(x,y)\bigr)\cdot\bigl(\sup_{x\neq y}\operatorname{ed}(x,y)/\|f(x)-f(y)\|_1\bigr)$.
--
--   Since $k=n^4/4$, the encoded mask words, which all have the same length, form a set of binary words with $\ell_1$ distortion at least $n^{n^4/4}$. This is the distortion part of the mask witness in the main theorem; combined with the bounds on the alphabet size and on the word length, it yields the lower bound of the form $\exp(c\sqrt{\log d\,\log\log d})$ for words of length at most $d$.
--
--   **Formalization Note** The prime array is `StandingPrimes (n^4) p`, $N$ is `circleSize (n^4) p`, the states are `MaskState (n^4) p N (n^4)`, the words are `maskWord (n^4) p ((n^4)^(2*n^4)) N (n^4) v`, the encoding is `encode c`, and $c_1$ is `setDistortion` of the range. In `maskGamma` the quotient $N/p_{l,s}$ is natural-number division, which is exact here because every $p_{l,s}$ divides $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BinaryDistortion.lean#L104-L143

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

theorem OAI.FiniteCircle.mask_binary_distortion {n k : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {w : ℕ}
    (c : MaskAlphabet (n^4) p (n^4) → Fin w → Bool)
    (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ setDistortion (Set.range fun v : MaskState (n^4) p (circleSize (n^4) p) (n^4) =>
      encode c (maskWord (n^4) p ((n^4)^(2*n^4)) (circleSize (n^4) p) (n^4) v)) := by sorry
