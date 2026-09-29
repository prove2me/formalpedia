-- Prove2me | Theorems.Thm_Module_Free_of_surjective_of_smul_eq
-- name    : Module.Free.of_surjective_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/35faf021-bd81-5cf6-a8f4-4e4d0a59dff8
-- title:
--   Freeness descends along a surjective ring map compatible with scalars
-- statement:
--   Let $S$ be a commutative ring, $T$ a ring, and $N$ an additive abelian group carrying both an $S$-module structure and a $T$-module structure, and suppose $N$ is free as an $S$-module. Let $g\colon S \to T$ be a ring homomorphism such that the two actions on $N$ agree through $g$, i.e. $g(s) \cdot n = s \cdot n$ for all $s \in S$ and $n \in N$, and suppose $g$ is surjective. The conclusion is that $N$ is free as a $T$-module. No finiteness or commutativity assumption is placed on $T$, and no compatibility between the two module structures is assumed beyond the displayed identity for elements of the image of $g$; in particular $T$ is not assumed to be an $S$-algebra and $N$ need not be finitely generated.
--
--   A transfer-of-freeness lemma of elementary commutative algebra, used to convert freeness of a module over one ring into freeness over a quotient-like target through which the action factors. It is cited by [`Algebra.PatchingDatum.bijective_and_free_of_surjective`](thm.html#Algebra.PatchingDatum.bijective_and_free_of_surjective), where freeness of a patched module over a deformation ring is carried across to freeness over the associated Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Free_of_surjective_of_smul_eq.lean

import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Module.Free.of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) : Module.Free T N := by sorry
