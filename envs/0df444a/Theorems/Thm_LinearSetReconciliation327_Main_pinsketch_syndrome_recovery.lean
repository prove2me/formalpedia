-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery
-- name    : LinearSetReconciliation327.Main.pinsketch_syndrome_recovery
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:09:43.842972+00:00
-- url     : https://prove2.me/theorems/c3f9b4b4-d025-4824-a694-df0c7dc66d50
-- title:
--   Pinsketch recovery: a light vector is determined by its syndrome
-- statement:
--   Let $F$ be a field of characteristic two (a $\mathbb{Z}_2$-algebra), let $(\iota_0,\dots,\iota_{N-1})$ be nonzero elements of $F$ that are pairwise distinct, and let $t$ be a weight parameter. For a vector $x \in \mathbb{Z}_2^{N}$ of Hamming weight at most $t$, the Pinsketch syndrome is
--
--   $$
--   \operatorname{pin}_{\iota,t}(x) = \Bigl(\sum_{i:\,x_i=1} \iota_i^{\,2j+1}\Bigr)_{j=0}^{t-1} \in F^{t}.
--   $$
--
--   The theorem asserts that this map is injective on the set of vectors of weight at most $t$: if $x,x' \in \mathbb{Z}_2^{N}$ both have Hamming weight at most $t$ and $\operatorname{pin}_{\iota,t}(x)=\operatorname{pin}_{\iota,t}(x')$, then $x=x'$.
--
--   Equivalently, a $t$-light vector is fully determined by its $t$ odd power sums. This is the recovery (uniqueness) property of the Pinsketch sketch, and it is the fourth conjunct of Proposition 2.1; the decoding program is required to return *the* light vector whose syndrome it was given, so this uniqueness is what makes "the" answer well defined.
--
--   **Formalization Note** The characteristic-two hypothesis is carried by the typeclass assumption `[Algebra (ZMod 2) F]`; `pin` is the power-sum map above and `x i = 1` is membership in the support of a $\mathbb{Z}_2$-vector.
-- source:
--   arXiv:2611.11409, Section 2.2, Proposition 2.1 (recovery conjunct), and Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_syndrome_recovery
    {F : Type} [Field F] [Algebra (ZMod 2) F] {N t : ℕ} (ι : ℕ → F)
    (h0 : ∀ v < N, ι v ≠ 0) (hinj : Set.InjOn ι (Set.Iio N)) {x x' : Fin N → ZMod 2}
    (hx : (univ.filter fun i => x i = 1).card ≤ t)
    (hx' : (univ.filter fun i => x' i = 1).card ≤ t)
    (hp : pin ι t x = pin ι t x') : x = x' := by sorry
