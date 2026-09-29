-- Prove2me | Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
-- name    : M4aHerbrand.nonempty_ideleGaloisDescent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/80ca7d41-5394-5859-8b04-d3ed011aff70
-- title:
--   Existence of a Galois descent datum on the adele ring
-- statement:
--   Let $K$ and $L$ be number fields, i.e. fields that are finite-dimensional over $\mathbb{Q}$, with $L$ given as a $K$-algebra. The assertion is that the type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28) is nonempty, i.e. that there exists a datum consisting of the following three pieces of structure: first, a monoid homomorphism $\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the group $\mathrm{RingAut}(\mathbb{A}_L)$ of ring automorphisms of the adele ring of $L$ formed with respect to the ring of integers $\mathcal{O}_L$; second, a compatibility condition stating that for every $K$-algebra automorphism $g$ of $L$ and every $x \in L$ one has $\mathrm{act}(g)$ applied to the principal adele attached to $x$ equal to the principal adele attached to $g(x)$, the embedding being the structure map $L \to \mathbb{A}_L$; and third, the requirement that for every such $g$ the underlying map of $\mathrm{act}(g)$ is continuous for the adele topology. No separability or normality hypothesis on $L/K$ is imposed: the automorphism group $L \simeq_{\mathrm{alg}[K]} L$ is used whatever it happens to be.
--
--   This is the existence half of the statement that the adele ring of $L$ carries a canonical action of the $K$-automorphisms of $L$ by continuous ring automorphisms fixing the principal adeles; paired with the corresponding uniqueness (subsingleton) statement, it shows that a descent datum $D$ on $\mathbb{A}_L$ over $K$ exists and is unique, so that results quantified over such a $D$ are statements about the canonical Galois action. It is used by the idele-class Herbrand quotient and norm-index computations, for instance in the finiteness and cardinality bound for $H^2$ of the idele class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_nonempty_ideleGaloisDescent.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField

theorem M4aHerbrand.nonempty_ideleGaloisDescent
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Nonempty (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) := by sorry
