-- Prove2me | Theorems.Thm_Hatcher_Singular_mayerVietoris
-- name    : Hatcher.Singular.mayerVietoris
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:26:56.801339+00:00
-- url     : https://prove2.me/theorems/743b213c-2421-4197-9caf-689427e7be8b
-- title:
--   The Mayer–Vietoris sequence for singular homology
-- statement:
--   Let $R$ be a ring, $X$ a topological space and $A,B\subseteq X$ subsets whose interiors cover $X$. Write $i:A\cap B\hookrightarrow A$, $j:A\cap B\hookrightarrow B$, $k:A\hookrightarrow X$, $l:B\hookrightarrow X$ for the inclusions, and $H_n(\cdot)=H_n(\cdot\,;R)$ for singular homology with coefficients in $R$.
--
--   Then there are homomorphisms $\delta_n:H_{n+1}(X)\to H_n(A\cap B)$ such that the long sequence
--   $$\cdots\to H_{n+1}(X)\xrightarrow{\ \delta_n\ }H_n(A\cap B)\xrightarrow{\ (i_*,\,-j_*)\ }H_n(A)\oplus H_n(B)\xrightarrow{\ k_*+l_*\ }H_n(X)\xrightarrow{\ \delta_{n-1}\ }H_{n-1}(A\cap B)\to\cdots$$
--   is exact, that is, for every $n\ge 0$:
--
--   1. the kernel of $k_*+l_*$ on $H_n(A)\oplus H_n(B)$ is the image of $(i_*,-j_*)$;
--   2. the kernel of $\delta_n$ is the image of $k_*+l_*:H_{n+1}(A)\oplus H_{n+1}(B)\to H_{n+1}(X)$;
--   3. the kernel of $(i_*,-j_*)$ on $H_n(A\cap B)$ is the image of $\delta_n$.
--
--   The Mayer–Vietoris sequence is the main tool for computing homology by cutting a space into simpler pieces; it gives, for instance, the homology of spheres and of complex projective spaces.
--
--   **Formalization Note** The boundary maps are only asserted to exist. $H_n(A)\oplus H_n(B)$ is the product module, the maps are the underlying $R$-linear maps of the induced homomorphisms, and exactness is Mathlib's `Function.Exact`. The sequence ends with $H_0(X)\to 0$, which is not part of the statement.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.2, “Mayer–Vietoris Sequences” (pp. 149–150; the maps $\varphi(x)=(x,-x)$ and $\psi(x,y)=x+y$ are on p. 150), with coefficients as on p. 153. Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Singular/MayerVietoris.lean`.

import Mathlib
import Definitions.Def_Hatcher_SingularHomology

open CategoryTheory

theorem Hatcher.Singular.mayerVietoris (R : Type) [Ring R] (X : Type) [TopologicalSpace X] (A B : Set X)
    (hAB : interior A ∪ interior B = Set.univ) :
    ∃ δ : ∀ n : ℕ, H R (n + 1) X ⟶ H R n ↥(A ∩ B), ∀ n : ℕ,
      Function.Exact
        (LinearMap.prod
          (map R n (⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩ :
            C(↥(A ∩ B), A))).hom
          (-(map R n (⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩ :
            C(↥(A ∩ B), B))).hom))
        (LinearMap.coprod (map R n (incl A)).hom (map R n (incl B)).hom) ∧
      Function.Exact
        (LinearMap.coprod (map R (n + 1) (incl A)).hom (map R (n + 1) (incl B)).hom)
        (δ n).hom ∧
      Function.Exact (δ n).hom
        (LinearMap.prod
          (map R n (⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩ :
            C(↥(A ∩ B), A))).hom
          (-(map R n (⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩ :
            C(↥(A ∩ B), B))).hom)) := by sorry
