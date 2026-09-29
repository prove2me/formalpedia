-- Prove2me | Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
-- name    : LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/271124d8-2c5b-53fe-8fc1-0942e5ce9ac2
-- title:
--   Surjection with acyclic kernel induces isomorphisms on cohomology
-- statement:
--   Let $R$ be a commutative ring and let $C, D \colon \mathbb{N} \to \mathrm{Mod}_R$ be families of $R$-modules equipped with $R$-linear maps $d_C^n \colon C^n \to C^{n+1}$, $d_D^n \colon D^n \to D^{n+1}$ and $f^n \colon C^n \to D^n$ satisfying: $f^{n+1}(d_C^n x) = d_D^n(f^n x)$ for all $n$ and all $x \in C^n$; $d_C^{n+1}(d_C^n x) = 0$ for all $n$ and $x$; each $f^n$ is surjective; any $x \in C^0$ with $f^0 x = 0$ and $d_C^0 x = 0$ vanishes; and for every $n$, any $x \in C^{n+1}$ with $f^{n+1} x = 0$ and $d_C^{n+1} x = 0$ is of the form $x = d_C^n y$ for some $y \in C^n$ with $f^n y = 0$ (exactness of the kernel complex, expressed elementwise). The conclusion is twofold. First, there exists an $R$-linear isomorphism $e \colon \ker d_C^0 \to \ker d_D^0$ such that $e(x) = f^0 x$ in $D^0$ for every $x \in \ker d_C^0$. Secondly, for every $n$ there exists an $R$-linear isomorphism between $\ker d_C^{n+1}$ modulo the preimage of $\operatorname{range} d_C^n$ under the inclusion $\ker d_C^{n+1} \hookrightarrow C^{n+1}$ and the corresponding quotient for $D$, which carries the class of any $x \in \ker d_C^{n+1}$ to the class of any $y \in \ker d_D^{n+1}$ with $y = f^{n+1} x$ in $D^{n+1}$. No exactness or cocomplex condition is imposed on $D$ beyond what follows from the hypotheses on $C$ and $f$.
--
--   This is the statement that a degreewise surjective map of cochain complexes of $R$-modules whose kernel complex is acyclic induces isomorphisms on cohomology, i.e. the 'acyclic kernel implies quasi-isomorphism' case of the long exact cohomology sequence, phrased directly in the $\ker/\operatorname{im}$ presentation of cohomology rather than through homological algebra machinery. It is used in the comparison of Čech-type cohomology of presheaves of $\mathcal{O}$-modules, for instance to transport Čech equivalences along order embeddings, along pullbacks and twists, and along order isomorphisms of index sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    {R : Type u} [CommRing R] {C D : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
    (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
    (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
    (hsurj : ∀ n, Function.Surjective (f n))
    (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
    (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
      ∃ y : C n, f n y = 0 ∧ dC n y = x) :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by sorry
