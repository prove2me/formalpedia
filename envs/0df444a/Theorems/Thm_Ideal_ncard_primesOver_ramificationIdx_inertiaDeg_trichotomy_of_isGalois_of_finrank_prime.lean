-- Prove2me | Theorems.Thm_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
-- name    : Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/d0de8144-a8a1-5a6d-afe8-70f5ad7091c5
-- title:
--   Splitting trichotomy in Galois extensions of prime degree
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ such that $L/K$ is Galois, and suppose the degree $\ell = [L:K]$, computed as the $K$-rank of $L$, is a prime number. Let $\mathfrak{p}$ be a maximal ideal of the ring of integers $\mathcal{O}_K$ with $\mathfrak{p} \neq 0$, and let $\mathfrak{P}$ be a prime ideal of $\mathcal{O}_L$ lying over $\mathfrak{p}$. Write $g$ for the number of elements of the set of primes of $\mathcal{O}_L$ above $\mathfrak{p}$ (its `Set.ncard`), and let $e =$ `p.ramificationIdx' P` and $f =$ `p.inertiaDeg' P` be the ramification index and the inertia degree of $\mathfrak{P}$ over $\mathfrak{p}$ in the primed Mathlib normalisation. Then at least one of the following three alternatives holds: $(g,e,f) = (\ell,1,1)$, so $\mathfrak{p}$ splits completely; or $(g,e,f) = (1,\ell,1)$, so $\mathfrak{p}$ is totally ramified; or $(g,e,f) = (1,1,\ell)$, so $\mathfrak{p}$ is inert. The disjunction is stated as an inclusive one, without asserting that the cases are mutually exclusive.
--
--   This is the classical trichotomy for a prime of a number field in a Galois extension of prime degree: it splits completely, is totally ramified, or is inert. It is used in the treatment of local behaviour at primes in small-degree Galois extensions, for instance in [`NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime`](thm.html#NumberField.nonempty_algHom_adicCompletion_of_nontrivial_extension_of_prime) and in the comparison of twisted and weighted Hecke data at unramified primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hℓ : (Module.finrank K L).Prime)
    (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p] :
    ((p.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = Module.finrank K L ∧ p.inertiaDeg' P = 1) ∨
      ((p.primesOver (𝓞 L)).ncard = 1 ∧
        p.ramificationIdx' P = 1 ∧ p.inertiaDeg' P = Module.finrank K L) := by sorry
