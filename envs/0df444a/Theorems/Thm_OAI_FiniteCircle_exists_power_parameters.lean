-- Prove2me | Theorems.Thm_OAI_FiniteCircle_exists_power_parameters
-- name    : OAI.FiniteCircle.exists_power_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:30:22.258014+00:00
-- url     : https://prove2.me/theorems/5db69520-e2ee-4a94-9119-b82cf4324ad6
-- title:
--   Parameters $b\ge 2$, $H\ge 1$ with $d\le b^H$ and $4b\,(1024(\lfloor\log_2 b^H\rfloor+1)^2)^H\le e^{32\sqrt{\ln d\,\ln\ln d}}$
-- statement:
--   Let $d$ be a natural number with $\ln d\ge 16$, where $\ln$ is the natural logarithm (equivalently, $d\ge e^{16}$). Then there exist natural numbers $b\ge 2$ and $H\ge 1$ such that $d\le b^H$ and
--   $$4b\,\Bigl(1024\bigl(\lfloor\log_2(b^H)\rfloor+1\bigr)^2\Bigr)^{H}\le\exp\Bigl(32\sqrt{\ln d\cdot\ln\ln d}\Bigr).$$
--
--   This is the parameter choice behind an $\exp\bigl(O(\sqrt{\log d\,\log\log d})\bigr)$ upper bound for embedding edit distance into $\ell^1$. Words of length at most $d$ are padded to the common length $b^H$ and embedded by $H$ rounds of a lifting step, each of which multiplies the distortion by at most $1024(\lfloor\log_2 b^H\rfloor+1)^2$, starting from a factor of order $b$. The lemma shows that the branching factor $b$ and the depth $H$ can be balanced so that the accumulated distortion (with an extra factor $4$ to spare) stays below $\exp\bigl(32\sqrt{\ln d\,\ln\ln d}\bigr)$.
--
--   **Formalization Note** $\lfloor\log_2(b^H)\rfloor$ is `Nat.log 2 (b^H)`, the logarithms are `Real.log`, the square root is `Real.sqrt`, and $d$ is cast from $\mathbb{N}$ to $\mathbb{R}$; under the hypothesis $\ln d\ge 16$ all logarithms involved are positive, so no junk-value conventions are used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/UpperParameters.lean#L48-L166

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

theorem OAI.FiniteCircle.exists_power_parameters {d : ℕ} (hd : 16 ≤ Real.log d) :
    ∃ b H : ℕ, 2 ≤ b ∧ 1 ≤ H ∧ d ≤ b^H ∧
      (4 * (b:ℝ) * (1024 * ((Nat.log 2 (b^H) : ℝ)+1)^2)^H) ≤
        Real.exp (32 * Real.sqrt (Real.log d * Real.log (Real.log d))) := by sorry
