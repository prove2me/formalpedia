-- Prove2me | Theorems.Thm_OAI_FiniteCircle_histogram_embedding_step
-- name    : OAI.FiniteCircle.histogram_embedding_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:29:42.888355+00:00
-- url     : https://prove2.me/theorems/561df2fd-ac6d-4d28-9101-d4d8a56046a2
-- title:
--   Histogram lifting of $\ell^1$ embeddings of the subsequence deficit from length $m$ to length $bm$
-- statement:
--   Let $\alpha$ be a finite alphabet and fix a letter $a\in\alpha$. For finite words $u,v$ over $\alpha$ let $\operatorname{lcs}(u,v)$ be the length of a longest common subsequence of $u$ and $v$, and define the *deficit*
--   $$\operatorname{def}(u,v)=|u|-\operatorname{lcs}(u,v).$$
--   Write $\alpha^n$ for the set of words of length exactly $n$, and for a map $G:\alpha^n\to\mathbb{R}^N$ write $\|G(u)-G(v)\|_1=\sum_{i=1}^{N}|G(u)_i-G(v)_i|$.
--
--   Let $m\ge 1$, $b\ge 0$ and $M\ge 0$ be integers, let $\Lambda\ge 0$ be real, and let $F:\alpha^m\to\mathbb{R}^M$ satisfy
--   $$\operatorname{def}(u,v)\le\|F(u)-F(v)\|_1\le\Lambda\,\operatorname{def}(u,v)\qquad\text{for all }u,v\in\alpha^m.$$
--   Then there exist an integer $M'\ge 0$ and a map $F':\alpha^{bm}\to\mathbb{R}^{M'}$ such that for all $x,y\in\alpha^{bm}$
--   $$\operatorname{def}(x,y)\le\|F'(x)-F'(y)\|_1\le 16\,\bigl(\lfloor\log_2 m\rfloor+1\bigr)\bigl(b+16\,\Lambda\ln(m+1)\bigr)\operatorname{def}(x,y),$$
--   where $\ln$ denotes the natural logarithm.
--
--   In words: an $\ell^1$ embedding of the deficit on words of length $m$ that is non-contracting and expands by at most $\Lambda$ can be lifted to words that are $b$ times longer, and the new expansion factor is $O\bigl(\log m\cdot(b+\Lambda\log m)\bigr)$. This is the recursive step of an upper bound for embedding edit distance into $\ell^1$: iterating it from words of length $1$ (where indicator vectors already work) gives embeddings of the deficit on words of length $b^H$, and padding shorter words with a fresh letter turns these into embeddings of the edit distance on all words of length at most $d$ into $\ell^1$, with distortion $\exp\bigl(O(\sqrt{\log d\,\log\log d})\bigr)$.
--
--   **Formalization Note** Words of length $n$ are `List.Vector α n`, the $\ell^1$ distance $\sum_i|G(u)_i-G(v)_i|$ is `coordDist G u v`, and $\lfloor\log_2 m\rfloor$ is `Nat.log 2 m`. The deficit is defined with natural-number subtraction, but no truncation happens because $\operatorname{lcs}(u,v)\le|u|$. The letter $a$ is an explicit argument that is only used in the construction (to pad windows to length $m$), so it does not occur in the conclusion; the dimension $M$ is an implicit argument.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/HistogramEmbedding.lean#L12-L113

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

theorem OAI.FiniteCircle.histogram_embedding_step {α : Type*} [Fintype α] (a : α) {m M : ℕ}
    (hm : 0 < m) (b : ℕ) (F : List.Vector α m → Fin M → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hFlo : ∀ u v, (deficit u.val v.val : ℝ) ≤ coordDist F u v)
    (hFhi : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val) :
    ∃ M' : ℕ, ∃ F' : List.Vector α (b*m) → Fin M' → ℝ,
      ∀ x y, (deficit x.val y.val : ℝ) ≤ coordDist F' x y ∧
        coordDist F' x y ≤ (16 * (Nat.log 2 m + 1) *
          (b + 16 * Real.log ((m:ℝ)+1) * Λ)) * deficit x.val y.val := by sorry
