-- Prove2me | Theorems.Thm_OAI_FiniteCircle_StandingPrimes_excluded_alphabet_bound
-- name    : OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:58:42.479311+00:00
-- url     : https://prove2.me/theorems/2dce9ba0-a29c-4309-b21a-7bcb229ab1b9
-- title:
--   The level-$h$ excluded-residue alphabet has at most $h^{6h^2}$ letters
-- statement:
--   A *standing prime array* for $h$ is a function $p\colon\mathbb N\times\mathbb N\to\mathbb N$, $(l,s)\mapsto p_{l,s}$, such that (i) for $1\le l\le h$ and $0\le s<h$ the number $p_{l,s}$ is prime with $h^3<p_{l,s}\le 2h^3$; (ii) these $h^2$ primes are pairwise distinct; (iii) $p_{l,s}=1$ for every other pair $(l,s)$.
--
--   Given such an array, the *period* of level $l$ is $P_l=\prod_{s<h}p_{l,s}$ and the *circle size* is $N=2\prod_{l=1}^{h}P_l$. For parameters $m,L\in\mathbb N$ the *excluded alphabets* are $\mathcal B_0=\{0,\dots,L-1\}\times\{0,1\}$ and $\mathcal B_{l}=\{0,\dots,m-1\}\times\mathcal B_{l-1}$ for $l\ge1$.
--
--   Let $h\ge2$ and let $p$ be a standing prime array for $h$. Then the excluded alphabet of level $h$ with parameters $m=h$ and $L=N$ satisfies
--
--   $$
--   |\mathcal B_h|\;\le\;h^{6h^2}.
--   $$
--
--   The letters of the level-$h$ excluded-residue words lie in $\mathcal B_h$, so the bound controls the block length $w\le C\ln(2|\mathcal B_h|)$ of a binary code for this alphabet, exactly as for the mask alphabet.
--
--   **Formalization Note** The alphabet is `ExcludedAlphabet h (circleSize h p) h`, the circle size is `circleSize h p = 2 * ∏ l : Fin h, period h p (l+1)` with `period h p l = ∏ k : Fin h, p l k`, and $|\cdot|$ is `Fintype.card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L120-L133

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

theorem OAI.FiniteCircle.StandingPrimes.excluded_alphabet_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2≤h) :
    Fintype.card (ExcludedAlphabet h (circleSize h p) h) ≤ h^(6*h^2) := by sorry
