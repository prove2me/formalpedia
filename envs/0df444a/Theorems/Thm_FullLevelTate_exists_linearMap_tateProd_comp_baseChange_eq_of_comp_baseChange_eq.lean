-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/96c1b50f-7102-518e-9d00-24aef31a11ff
-- title:
--   Base change of an equivariant comparison map to K
-- statement:
--   Let $q$ and $\lambda$ be primes, $M'$ a natural number, and $O'$ a commutative $\mathbb{Z}_\lambda$-algebra. Write $T =$ [`TateModule lam (ModularCurve.FullLevel.Jac q M')`](def/EllipticCurve_TateModule.html#L15) for the group of sequences $(x_n)$ in $\mathbb{N} \to \mathrm{Jac}(q,M') = (\mathrm{Idx}\,q \to \mathrm{jacComp}\,q\,M')$ satisfying $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$. Let $R$ be a monoid homomorphism from $\mathrm{Gal} = \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to $\mathrm{End}_{O'}(O' \otimes_{\mathbb{Z}_\lambda} T)$ acting on pure tensors by $a \otimes x \mapsto a \otimes \mathrm{tateGal}(\sigma)x$, and $G$ a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Z}/q)$ to the same endomorphism monoid acting by $a \otimes x \mapsto a \otimes \mathrm{tateGL2}(g)x$. Let $K$ be a field that is both an $O'$- and a $\mathbb{Q}_\lambda$-algebra, the two structure maps agreeing on $\mathbb{Z}_\lambda$, and let $k$ be a field extension of $\mathrm{GF}(q^2)$ for which the Drinfeld coordinate ring $\mathrm{MvPolynomial}(\mathrm{Fin}\,2,k)/(\mathrm{drinfeldPoly}-1)$ is a domain. Fix an index type and a $\mathbb{Q}_\lambda$-linear map $sp_0 \colon \mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T \to \bigl(\mathrm{index} \to \mathbb{Q}_\lambda \otimes_{\mathbb{Q}_\lambda} V\bigr)$, where $V$ is the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of the fraction field of that coordinate ring. Then there is a $K$-linear map $sp \colon K \otimes_{O'} (O' \otimes_{\mathbb{Z}_\lambda} T) \to (\mathrm{index} \to K \otimes_{\mathbb{Q}_\lambda} V)$ with $sp(c \otimes (a \otimes x))_i = (\mathrm{algebraMap}\,a \cdot c) \otimes \mathrm{lid}(sp_0(1 \otimes x)_i)$ for all $c \in K$, $a \in O'$, $x \in T$ and all indices $i$, and such that for every $\tau \in \mathrm{Gal}$, every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ and every $\alpha \in \mathrm{GF}(q^2)^\times$ with $(g,\alpha)$ in the kernel of $(g,\alpha) \mapsto \det(g)\,\alpha^{q+1}$: if $sp_0$ intertwines the base change to $\mathbb{Q}_\lambda$ of $\mathrm{tateGL2}(g)\,\mathrm{tateGal}(\tau)$ with the componentwise action `tateProdRep` of $\langle (g,\alpha)\rangle$ over $\mathbb{Q}_\lambda$, then $sp$ intertwines the base change to $K$ of $G(g)R(\tau)$ with `tateProdRep` of the same element over $K$.
--
--   This is the transport step that moves a comparison map between the $\lambda$-adic Tate module of the full-level modular Jacobian and a product of Tate modules of the Drinfeld curve from $\mathbb{Q}_\lambda$-coefficients up to $K$-coefficients, preserving equivariance for the pairs in the relevant subgroup. It is used in the three statements producing level-automorphism inputs according as the relevant parameter is two, three, or at least five.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_of_comp_baseChange_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (R : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hR : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O')
      (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      R σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGal q M' lam σ x)
    (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam g x)
    (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)] (index : Type)
    (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] index) :
    ∃ sp : K ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')) →ₗ[K]
        DrinfeldCurve.tateProd q k lam K index,
      (∀ (c : K) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (i : index),
        sp (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) i =
          (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] TensorProduct.lid ℚ_[lam] _ (sp₀ ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) i)) ∧
      ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CuspidalType.GL2 q) (α : (GaloisField q 2)ˣ)
          (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
        sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g * ModularCurve.FullLevel.tateGal q M' lam τ).baseChange
              ℚ_[lam] = DrinfeldCurve.tateProdRep q k lam ℚ_[lam] index ⟨(g, α), hg⟩ ∘ₗ sp₀ →
          sp ∘ₗ ((G g * R τ).baseChange K) = DrinfeldCurve.tateProdRep q k lam K index ⟨(g, α), hg⟩ ∘ₗ sp := by sorry
