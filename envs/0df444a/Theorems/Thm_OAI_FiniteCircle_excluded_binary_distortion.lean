-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_binary_distortion
-- name    : OAI.FiniteCircle.excluded_binary_distortion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:03:57.048838+00:00
-- url     : https://prove2.me/theorems/e974490a-cd3e-4bc3-8344-bf58184a13cf
-- title:
--   Binary encodings of the excluded-prime circle words have $\ell^1$ distortion at least $n^{n^4/4}$
-- statement:
--   Let $n\ge10^6$ and $k\in\mathbb{N}$ with $n^4=4k$, and put $h=n^4$.
--
--   *Primes.* Let $p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ be a standing prime system for $h$: the numbers $p(l,s)$ with $1\le l\le h$ and $0\le s<h$ are pairwise distinct primes with $h^3<p(l,s)\le2h^3$, and $p(l,s)=1$ for every other pair $(l,s)$. Put $P_l=\prod_{s=0}^{h-1}p(l,s)$ and
--   $$
--   M=2\prod_{l=1}^{h}P_l,\qquad R=h^{2h}.
--   $$
--
--   *States and words.* Define alphabets $\Sigma_0=\{0,\dots,M-1\}\times\{0,1\}$ and $\Sigma_{l+1}=\{0,\dots,h-1\}\times\Sigma_l$, and state spaces $\mathcal V_0=\mathbb{Z}/M\mathbb{Z}$ and $\mathcal V_{l+1}=(\mathcal V_l)^{\{0,\dots,h-1\}}$; thus a state of level $l$ assigns a phase in $\mathbb{Z}/M\mathbb{Z}$ to every leaf of the rooted tree of depth $l$ in which each internal node has $h$ children. For $v\in\mathcal V_l$ and $\theta\in\mathbb{Z}/M\mathbb{Z}$ let $v+\theta$ be the state obtained by adding $\theta$ to every phase. For a level $l+1\ge1$, $a\in\mathbb{N}$ and $0\le i<h$ define the translations
--   $$
--   \tau_{l+1}(a,i)=\sum_{j\ne i}\frac{M}{p(l+1,j)}\,\bigl(a\bmod p(l+1,j)\bigr)\in\mathbb{Z}/M\mathbb{Z},
--   $$
--   where $j$ ranges over $\{0,\dots,h-1\}\setminus\{i\}$. Words $W_l(v)$ over $\Sigma_l$ are defined recursively.
--   - For $v\in\mathcal V_0$, $W_0(v)$ has length $M$, and its letter at position $b\in\{0,\dots,M-1\}$ is $(b,\beta_b)$, where $\beta_b=1$ exactly when the residue of $b-v$ in $\{0,\dots,M-1\}$ is less than $M/2$: a position-tagged indicator of the half circle starting at $v$.
--   - For $v=(v_0,\dots,v_{h-1})\in\mathcal V_{l+1}$, the word $W_{l+1}(v)$ is the concatenation of the rows $a=0,1,\dots,RP_{l+1}-1$, where row $a$ is the concatenation over $i=0,\dots,h-1$ of the words $W_l\bigl(v_i+\tau_{l+1}(a,i)\bigr)$ with every letter $z$ replaced by $(i,z)$.
--
--   So the subtree of child $i$ is translated by phases coming from all primes of its level except the excluded one, $p(l+1,i)$.
--
--   *Codes, edit distance and distortion.* For words $x,y$ let $\operatorname{ed}(x,y)$ be the edit distance (least number of single-letter insertions, deletions and substitutions turning $x$ into $y$), $\operatorname{lcs}(x,y)$ the maximal length of a common subsequence, and $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$. Let $c:\Sigma_h\to\{0,1\}^w$ be a binary block code and $\operatorname{enc}_c(x)$ the concatenation of the codewords of the letters of $x$. Assume $c$ satisfies the substitution bounds with constants $a_0=2^{-28}=1/268435456$ and $C_0=67108928$:
--   - $w>0$ and $w\le C_0\log\bigl(2|\Sigma_h|\bigr)$ (natural logarithm);
--   - $a_0\,w\operatorname{def}(x,y)\le\operatorname{def}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{def}(x,y)$ for all words $x,y$ over $\Sigma_h$ of equal length;
--   - $\operatorname{ed}(\operatorname{enc}_cx,\operatorname{enc}_cy)\le w\operatorname{ed}(x,y)$ for all words $x,y$ over $\Sigma_h$.
--
--   For a set $\mathcal S$ of binary words, its optimal $\ell^1$ distortion is
--   $$
--   c_1(\mathcal S)=\inf_{f}\ \Bigl(\sup_{s\ne t}\frac{\|f(s)-f(t)\|_1}{\operatorname{ed}(s,t)}\Bigr)\Bigl(\sup_{s\ne t}\frac{\operatorname{ed}(s,t)}{\|f(s)-f(t)\|_1}\Bigr),
--   $$
--   where $f$ ranges over the injective maps from $\mathcal S$ into the space $\ell^1(\mathbb{N})$ of summable real sequences, and $s,t$ range over $\mathcal S$.
--
--   **Theorem.** Under these assumptions,
--   $$
--   n^{k}\ \le\ c_1\Bigl(\bigl\{\operatorname{enc}_c\bigl(W_h(v)\bigr):\ v\in\mathcal V_h\bigr\}\Bigr).
--   $$
--
--   Since $k=n^4/4$, the binary family has optimal $\ell^1$ distortion at least $n^{n^4/4}$, for every binary code satisfying the substitution bounds. In the main theorem this is applied with the anchor-local binary code to obtain the excluded witness family, whose distortion is then compared with $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$ for the relevant word lengths $d$.
--
--   **Formalization Note** In Lean, $\Sigma_l$, $\mathcal V_l$ and $W_l$ are `ExcludedAlphabet h M l`, `ExcludedState h M l` and `excludedWord h p R M l`; $M$ is `circleSize h p`, the standing prime system is `StandingPrimes h p`, and the substitution bounds are `SubstitutionBounds (1/268435456) 67108928 c`. The bit $\beta_b$ is `decide (((b : ZMod M) - v).val < M / 2)` with natural-number division. The distortion $c_1$ is `setDistortion`, defined through `sSup` and `sInf` on $\mathbb{R}$; here the family is finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/BinaryDistortion.lean#L144-L183

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

theorem OAI.FiniteCircle.excluded_binary_distortion {n k : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {w : ℕ}
    (c : ExcludedAlphabet (n^4) (circleSize (n^4) p) (n^4) → Fin w → Bool)
    (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ setDistortion (Set.range fun v : ExcludedState (n^4) (circleSize (n^4) p) (n^4) =>
      encode c (excludedWord (n^4) p ((n^4)^(2*n^4)) (circleSize (n^4) p) (n^4) v)) := by sorry
