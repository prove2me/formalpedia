-- Prove2me | Theorems.Thm_NumberField_denseRange_algebraMap_add_adeleSingleAt
-- name    : NumberField.denseRange_algebraMap_add_adeleSingleAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/391cd4cd-0602-5093-8543-a2501c82627b
-- title:
--   Additive strong approximation away from one finite place
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $v$ be a point of the height one spectrum of $\mathcal{O}_K$, i.e. a nonzero prime ideal, equivalently a finite place of $K$. Consider the map from $K \times K_v$ to the adele ring of $K$ (the product of the infinite adele ring of $K$ with the finite adele ring of $\mathcal{O}_K$ in $K$), where $K_v$ denotes the $v$-adic completion, which sends a pair $(a, y)$ to the sum of the principal adele $\operatorname{algebraMap} a$ attached to $a \in K$ and the adele `adeleSingleAt K v y`; the latter is by definition the image under the inclusion $x \mapsto (0, x)$ of the finite adele `finAdeleSingleAt K v y`, which is the element of the restricted product of the completions $K_w$ with respect to the rings of integers $\mathcal{O}_w$ having component $y$ at $v$ and component $0$ at every other finite place. The assertion is that this map has dense range: every adele of $K$ lies in the closure of the set of sums of a principal adele and an adele whose components away from $v$ — including all the archimedean ones — vanish.
--
--   This is the additive strong approximation theorem for a number field with one finite place removed: $K$ is dense in the adeles with the $v$-component deleted. It serves in the construction and comparison of local and global additive characters and their associated constants, and is used in the proof that no function can satisfy the relevant system of Hecke eigenvalue identities at a genuine cuspidal realization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_denseRange_algebraMap_add_adeleSingleAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.denseRange_algebraMap_add_adeleSingleAt (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    DenseRange fun qy : K × v.adicCompletion K =>
      algebraMap K (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt K v qy.2 := by sorry
