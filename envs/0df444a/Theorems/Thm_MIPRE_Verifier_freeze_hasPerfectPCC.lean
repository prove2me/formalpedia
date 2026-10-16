-- Prove2me | Theorems.Thm_MIPRE_Verifier_freeze_hasPerfectPCC
-- name    : MIPRE.Verifier.freeze_hasPerfectPCC
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:31:51.46802+00:00
-- url     : https://prove2.me/theorems/c0be4f05-9b8c-4444-8fbe-f8db8f80d07b
-- title:
--   Freezing a verifier at an index preserves perfect PCC strategies: the frozen verifier has one at any index iff the original has one at the frozen index
-- statement:
--   A normal-form verifier $V$ with $\ell$ levels (`Verifier ℓ`) is a sampler and a decider, two programs of the ambient model; at index $n$ its game $\mathcal{V}_n$ with answers of length at most $T$ (`V.game n T`) has questions $\mathbb{F}_2^{s(n)}$, with $s(n)$ the sampler's dimension, distributed as the sampler prescribes, and accepts $(x, y, a, b)$ when the decider accepts $(n, x, y, a, b)$. The doubled game `V.doubledGame n T` plays on $\mathrm{Bool} \times \mathbb{F}_2^{s(n)}$: the pair $((\mathrm{false}, x), (\mathrm{true}, y))$ has the weight of $(x, y)$ and is decided as $(x, y)$ is, every other pair has weight zero and is rejected; it is a synchronous game for every $V$. $V$ has a perfect PCC strategy at index $n$ and answer bound $T$ (`V.HasPerfectPCC n T`) when some synchronous strategy of the doubled game, a single family of projective measurements played by both players and measured in the tracial state, is PCC (commuting on the support of the question distribution) and has value $1$. The verifier frozen at index $k$, `V.freeze k`, has sampler and decider programs that, on any input $(N, d)$, run the original programs on $(k, d)$: at every index it presents the dimension, the CL functions and the acceptance of $V$ at index $k$. For all $k, n, T \in \mathbb{N}$,
--
--   $$ \mathrm{HasPerfectPCC}\bigl(V^{\mathrm{frz}\,k},\ n,\ T\bigr)\ \iff\ \mathrm{HasPerfectPCC}(V,\ k,\ T). $$
--
--   Freezing is item 2 of blueprint `rem:compression-abstract`: the compressibility criterion recurses $n \to 2n+1$ while gap-preserving compression relates the game at index $2^n$ to the output at index $n$, and freezing the described verifier at $2n+1$ before compressing reconciles the two, the frozen verifier's game at index $2^n$ being the original's at level $2n+1$. This theorem is the transfer of perfect PCC strategies across that step, the companion of `freeze_valStar` for the value.
--
--   **Formalization Note** The statement is `MIPRE.Verifier.freeze_hasPerfectPCC`, with `ℓ` implicit and `V : Verifier ℓ`, `k n T` explicit. `HasPerfectPCC n T` unfolds to `∃ S : SyncStrategy (V.doubledGame n T), S.IsPCC ∧ S.value = 1`; `V.freeze k` has `sampler := V.sampler.freeze k` and `decider := V.decider.freeze k`, both with programs `Prog.freezeProg k _`, and `(V.freeze k).sampler.dim n = V.sampler.dim k` definitionally, so the two question types agree. The equivalence holds at every `n`, with no boundedness or synchronicity hypothesis.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Freeze.lean#L219-L238; internal lemma of the formalization of blueprint rem:compression-abstract, item 2 (freezing a verifier at an index), used in thm:halting, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
variable {ℓ : ℕ} (V : Verifier ℓ)

theorem MIPRE.Verifier.freeze_hasPerfectPCC (k n T : ℕ) :
    (V.freeze k).HasPerfectPCC n T ↔ V.HasPerfectPCC k T := by sorry
