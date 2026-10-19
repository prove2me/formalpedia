-- Prove2me | Theorems.Thm_OAI_FiniteCircle_lower_numeric
-- name    : OAI.FiniteCircle.lower_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:00:53.862905+00:00
-- url     : https://prove2.me/theorems/04793029-6926-403d-a607-a90e9c6419d6
-- title:
--   The numerical hypothesis of the Fourier distortion bound forces $t\ge n^{k}$ when $n^4=4k$
-- statement:
--   Let $n,k,M,w$ be natural numbers with $n\ge10^6$, $n^4=4k$, $w>0$ and $\lfloor\log_2 M\rfloor+1\le n^{13}$, and write $J=\lfloor\log_2 M\rfloor+1$. Let $t$ be a real number such that
--
--   $$
--   \frac{2^{-28}\,w}{n^{3n^4}}\;\le\;t\,w\left(\frac{4n^4}{(n^4)^{2n^4}}+\frac{2J}{(n^4/2)^{n^4}}\right).
--   $$
--
--   Then $n^k\le t$.
--
--   The displayed hypothesis is exactly the numerical condition of the Fourier-analytic lower bound for $\ell_1$ distortion, specialised to the long-direction separation $\delta=2^{-28}w\,n^{-3n^4}$, the scale $u=w$, the depth $h=n^4$, the repetition factor $R=(n^4)^{2n^4}$ and the frequency threshold $B=(n^4/2)^{n^4}$, where $w$ is the block length of a binary code. The lemma therefore identifies the resulting distortion lower bound as $n^k=n^{n^4/4}$.
--
--   **Formalization Note** $\lfloor\log_2 M\rfloor$ is `Nat.log 2 M`, which equals $0$ for $M\le 1$; the constant $2^{-28}$ appears as `1/268435456`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Parameters.lean#L274-L290

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

theorem OAI.FiniteCircle.lower_numeric {n k M : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13) {w : ℕ} (hw : 0<w) (t : ℝ)
    (ht : (1/268435456)*(w:ℝ)/(n:ℝ)^(3*n^4) ≤ t*w*
      (4*(n^4:ℕ)/((n^4:ℕ):ℝ)^(2*n^4)+2*(Nat.log 2 M+1:ℕ)/(((n^4:ℕ):ℝ)/2)^(n^4))) :
    (n:ℝ)^k ≤ t := by sorry
