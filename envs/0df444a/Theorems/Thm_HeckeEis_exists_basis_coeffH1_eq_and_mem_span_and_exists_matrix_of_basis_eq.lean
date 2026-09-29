-- Prove2me | Theorems.Thm_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
-- name    : HeckeEis.exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/2b3e55af-7218-5f98-aa27-60cd9c36865e
-- title:
--   Integral basis of coefficient cohomology with integral Hecke matrices
-- statement:
--   Let $R$ be a principal ideal domain, $K$ a field with an $R$-algebra structure whose structure map $R \to K$ is injective, and $N$ a natural number for which $\Gamma_0(N)$ is finitely generated as a group. Let $\Lambda$ be an $R$-module carrying a representation $\rho_R$ of $\Gamma_0(N)$ and $V$ a $K$-vector space carrying a representation $\rho$, and let $\iota \colon \Lambda \to V$ be an additive map satisfying $\iota(r \cdot x) = \mathrm{algebraMap}\,r \cdot \iota(x)$ for $r \in R$ and $\iota(\rho_R(\gamma)x) = \rho(\gamma)(\iota x)$; assume $\Lambda$ has an $R$-basis $(b^{\Lambda}_j)_{j \in \mathrm{Fin}\,d}$ and $V$ a $K$-basis $(b^{V}_j)_{j \in \mathrm{Fin}\,d}$ with $b^{V}_j = \iota(b^{\Lambda}_j)$. Here [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) of a representation is the quotient of the module of functions $z$ with $z(gh) = z(g) + \rho(g)z(h)$ by those lying in the image of the coboundary map, with [`HeckeEis.coeffH1Mk`](def/Gamma0CoeffCohomologyEigen.html#L27) the quotient map. Let $\Phi$ be an additive map from [`HeckeEis.coeffH1 ρR`](def/Gamma0CoeffCohomologyEigen.html#L16) to [`HeckeEis.coeffH1 ρ`](def/Gamma0CoeffCohomologyEigen.html#L16) induced by $\iota$ on cocycles, in the sense that every $\Lambda$-valued cocycle $z$ admits a $V$-valued cocycle $w$ with $w(\gamma) = \iota(z(\gamma))$ for all $\gamma$ and $\Phi[z] = [w]$. Let $I$ be a type and $(T_l^{R}, T_l)_{l \in I}$ additive endomorphisms of the two cohomology groups with $\Phi \circ T^{R}_l = T_l \circ \Phi$. Then there exist $t \in \mathbb{N}$, classes $b_1,\dots,b_t$ in [`HeckeEis.coeffH1 ρR`](def/Gamma0CoeffCohomologyEigen.html#L16) and a $K$-basis $c$ of [`HeckeEis.coeffH1 ρ`](def/Gamma0CoeffCohomologyEigen.html#L16) indexed by $\mathrm{Fin}\,t$ with $c_i = \Phi(b_i)$, such that every element of the image of $\Phi$ is of the form $\sum_i \mathrm{algebraMap}(r_i)\, c_i$ with $r_i \in R$, and for each $l \in I$ there is a matrix $A$ over $R$ with $T_l(c_j) = \sum_i \mathrm{algebraMap}(A_{ij})\, c_i$ for all $j$.
--
--   This is the integrality statement underlying reduction of Hecke eigensystems: the image of the cohomology of an $R$-form $\Lambda$ inside the cohomology of $V$ is an $R$-lattice spanned by a $K$-basis, with respect to which all the operators $T_l$ have matrices over $R$. It is used in the passage from eigensystems over a discrete valuation ring to eigensystems over its residue field, and in the corresponding reduction for the Steinberg quotient in positive characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq.lean

import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_basis_coeffH1_eq_and_mem_span_and_exists_matrix_of_basis_eq
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type} [Field K] [Algebra R K] (hRK : Function.Injective (algebraMap R K))
    (N : ℕ) [Group.FG (Gamma0 N)]
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {V : Type} [AddCommGroup V] [Module K V]
    (ρR : Representation R (Gamma0 N) Λ) (ρ : Representation K (Gamma0 N) V)
    (ι : Λ →+ V) (hιs : ∀ (r : R) (x : Λ), ι (r • x) = algebraMap R K r • ι x)
    (hιρ : ∀ (γ : Gamma0 N) (x : Λ), ι (ρR γ x) = ρ γ (ι x))
    {d : ℕ} (bΛ : Module.Basis (Fin d) R Λ) (bV : Module.Basis (Fin d) K V)
    (hb : ∀ j : Fin d, bV j = ι (bΛ j))
    (Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ)
    (hΦ : ∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ),
      (∀ γ : Gamma0 N, (w : Gamma0 N → V) γ = ι ((z : Gamma0 N → Λ) γ)) ∧
        Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ w)
    {I : Type} (TR : I → (HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρR))
    (T : I → (HeckeEis.coeffH1 ρ →+ HeckeEis.coeffH1 ρ))
    (hT : ∀ (l : I) (x : HeckeEis.coeffH1 ρR), Φ (TR l x) = T l (Φ x)) :
    ∃ (t : ℕ) (b : Fin t → HeckeEis.coeffH1 ρR) (c : Module.Basis (Fin t) K (HeckeEis.coeffH1 ρ)),
      (∀ i : Fin t, c i = Φ (b i)) ∧
        (∀ x : HeckeEis.coeffH1 ρR, ∃ r : Fin t → R, Φ x = ∑ i : Fin t, algebraMap R K (r i) • c i) ∧
          ∀ l : I, ∃ A : Matrix (Fin t) (Fin t) R,
            ∀ j : Fin t, T l (c j) = ∑ i : Fin t, algebraMap R K (A i j) • c i := by sorry
