-- Prove2me | Theorems.Thm_MIPRE_Verifier_hasPerfectPCC_of_accepts_iff
-- name    : MIPRE.Verifier.hasPerfectPCC_of_accepts_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:34.242409+00:00
-- url     : https://prove2.me/theorems/aea19708-dab8-4b70-83a4-de759368a030
-- title:
--   Perfect PCC strategies transfer between verifiers with the same sampler and equivalent deciders
-- statement:
--   Let $V$ and $W$ be $\ell$-level normal form verifiers, each a sampler (a program producing the questions) and a decider (a program checking the answers). Fix an index $n$ and an answer-length bound $T$. `V.HasPerfectPCC n T` says that the game $\mathcal{V}_n$ with answers of length at most $T$, played on the *doubled* question set (Alice is asked $(\mathtt{false}, x)$ and Bob $(\mathtt{true}, y)$ with $(x, y)$ distributed by the sampler; every other pair has weight $0$ and is rejected), has a synchronous strategy, one family of projective measurements indexed by the questions and used by both players against the tracial state, that is PCC (the measurements of any two questions asked with positive probability commute) and has value exactly $1$. Suppose $W$ has the same sampler as $V$ and that, for all bit strings $x, y, a, b$, $V$'s decider accepts $(n, x, y, a, b)$ if and only if $W$'s does. Then
--
--   $$ V.\mathrm{HasPerfectPCC}\ n\ T \;\Longrightarrow\; W.\mathrm{HasPerfectPCC}\ n\ T . $$
--
--   This is bookkeeping for the instantiation of the compressibility criterion (blueprint `rem:compression-abstract`): the verifier a string denotes and the verifier it is compared with share the compressed sampler and accept the same tuples at the index, so a completeness clause (a value-$1$ PCC strategy) proved for one holds for the other. The two-sided form is `hasPerfectPCC_congr`; the statements for $\mathrm{val}^*$ are `valStar_le_of_accepts_imp` and `valStar_congr`.
--
--   **Formalization Note** `Verifier.HasPerfectPCC n T := ∃ S : SyncStrategy (V.doubledGame n T), S.IsPCC ∧ S.value = 1`, where `V.doubledGame n T = (V.game n T).doubled` is a `SynchronousGame (Bool × V.Questions n) (Answers T)` with `Questions n = Fin (V.sampler.dim n) → 𝔽₂` and `Answers T = {a : BitStr // a.length ≤ T}`; the doubled game is synchronous for every verifier, so no synchronicity hypothesis on the decider is made. `SyncStrategy.IsPCC` is `∀ x y, 0 < G.μ x y → ∀ a b, M x a * M y b = M y b * M x a` (projectivity is part of `SyncStrategy`, consistency is automatic). `Decider.Accepts n x y a b := ∃ t, D.prog.Runs (encode (n, x, y, a, b)) (encode true) t`. The hypotheses are `hS : W.sampler = V.sampler` (propositional equality of `CL.Sampler ℓ`), `h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b` and `hV : V.HasPerfectPCC n T`; `V W n T` are implicit and `ℓ` is a section variable. Namespace `MIPRE.Verifier`, module `MIPRE.Foundations.VerifierValue`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/VerifierValue.lean#L81-L100

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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue

open MIPRE
open MIPRE.Verifier
open MIPRE.Cost
variable {ℓ : ℕ} (V : Verifier ℓ)

theorem MIPRE.Verifier.hasPerfectPCC_of_accepts_iff {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by sorry
