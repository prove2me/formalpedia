-- Prove2me | Theorems.Thm_OAI_FiniteCircle_histogram_forward_bound
-- name    : OAI.FiniteCircle.histogram_forward_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:28:11.657257+00:00
-- url     : https://prove2.me/theorems/3011ef4a-d7c8-4fe9-acd0-be140dee61e0
-- title:
--   A forward slide changes the windowed histograms at scale $s$ by at most $2b+32\log(s+1)\Lambda$ in expectation
-- statement:
--   **Setting.** Let $\alpha$ be an alphabet, $a\in\alpha$ a fixed padding letter, and $m,s$ natural numbers with $1\le s\le m$. Write $\alpha^{m}$ for the set of words of length exactly $m$. For words $x,y$ let $\operatorname{lcs}(x,y)$ be the length of a longest common subsequence and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$ the deficit. For a word $x$ and natural numbers $p,\ell$, the segment $x[p,p+\ell)$ consists of the letters of $x$ in positions $p,\dots,p+\ell-1$ (positions counted from $0$; the segment is shorter if $x$ ends earlier).
--
--   - *Normalisation.* For any word $z$, $N(z)\in\alpha^{m}$ consists of the first $m$ letters of $z$ followed by copies of $a$ up to length $m$.
--   - *Windows.* For a word $x$ and an offset $p$, the window list $\mathcal W_p(x)=\bigl(N(x[p+r,\,p+r+m-s+1))\bigr)_{r=0}^{s-1}$ consists of the $s$ normalised segments of length $m-s+1$ starting at the consecutive offsets $p,\dots,p+s-1$.
--   - *Base embedding.* $F:\alpha^{m}\to\mathbb{R}^{\iota}$, with $\iota$ a finite index set and $\Lambda\ge0$, satisfies $\|F(u)-F(v)\|_1=\sum_{i\in\iota}|F(u)_i-F(v)_i|\le\Lambda\,\operatorname{def}(u,v)$ for all $u,v\in\alpha^{m}$.
--   - *Random partition.* $\mu$ is a finite probability law on a finite set $\Omega$ (nonnegative weights with total $1$), $Y$ is a finite set, and $(\omega,u)\mapsto\operatorname{label}_\omega(u)\in Y$ is a random labelling of $\alpha^{m}$ with $\mu\{\omega:\operatorname{label}_\omega(u)=\operatorname{label}_\omega(v)\}=\exp\bigl(-\lambda_s\|F(u)-F(v)\|_1\bigr)$ for all $u,v\in\alpha^{m}$, where $\lambda_s=4\log(s+1)/s$.
--   - *Histogram distance.* For finite sequences $\mathbf x,\mathbf x'$ in $\alpha^{m}$ and a labelling $\ell$, $\operatorname{hd}_\ell(\mathbf x,\mathbf x')=\sum_{y\in Y}|H_\ell(\mathbf x)(y)-H_\ell(\mathbf x')(y)|$, where $H_\ell(\mathbf x)(y)$ is the number of entries of $\mathbf x$ with label $y$.
--
--   **Theorem.** Let $u,v,t$ be words, $c,d\in\alpha$ letters and $b\in\mathbb{N}$, and put
--   $$x=u\,c\,v\,t,\qquad y=u\,v\,d\,t,$$
--   so that $y$ arises from $x$ by deleting the letter $c$ in position $|u|$ and inserting the letter $d$ right after the block $v$. Then
--
--   $$
--   \sum_{j=0}^{b-1}\mathbb{E}_{\omega\sim\mu}\Bigl[\operatorname{hd}_{\operatorname{label}_\omega}\bigl(\mathcal W_{jm}(x),\,\mathcal W_{jm}(y)\bigr)\Bigr]\ \le\ 2b+32\log(s+1)\,\Lambda .
--   $$
--
--   The left-hand side is, up to a factor $4$, the contribution of the window scale $s$ to the $\ell^1$ distance between $x$ and $y$ in the next level of the recursive histogram embedding, in which words are cut into $b$ blocks of length $m$. The theorem says that such a move (a forward "slide"; the backward direction follows by symmetry of $\operatorname{hd}$) costs $O(1)$ per block plus $O(\log(s+1)\,\Lambda)$ in total. Since two words of equal length are joined by a chain of $2\operatorname{def}(x,y)$ slides, this yields the expansion bound of the new embedding.
--
--   **Formalization Note** Words of length $m$ are `List.Vector α m`, $N$ is `normalizeWord a m`, $\mathcal W_p(x)$ is `windowWords a x p m s`, $\|F(u)-F(v)\|_1$ is `coordDist F u v`, and $\lambda_s$ is `partitionRate s`; the words are `u ++ c :: (v ++ t)` and `u ++ v ++ d :: t`. No relation between $|x|$ and $bm$ is assumed: windows running past the end of a word are shorter segments, padded with $a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Separation.lean#L196-L252

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
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation

open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem OAI.FiniteCircle.histogram_forward_bound {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    (u v t : List α) (c d : α) (b : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (∑ j : Fin b, μ.expect (fun ω => histDist (label ω)
      (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
      (windowWords a (u ++ v ++ d :: t) (j*m) m s))) ≤
      2*b + 32 * Real.log ((s:ℝ)+1) * Λ := by sorry
