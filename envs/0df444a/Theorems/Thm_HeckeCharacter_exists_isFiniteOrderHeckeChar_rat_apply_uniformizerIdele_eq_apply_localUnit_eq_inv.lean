-- Prove2me | Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
-- name    : HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ad0f2d51-f242-5e7b-91bd-8b9203f67f35
-- title:
--   Idelic Hecke character attached to a Dirichlet character mod qᵇ
-- statement:
--   Let $q$ be a prime, let $b$ be a natural number and let $\chi_0 \colon (\mathbb{Z}/q^b\mathbb{Z})^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism. Then there exists a homomorphism $\eta$ from the unit group of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ with the following five properties. First, $\eta$ satisfies `IsFiniteOrderHeckeChar`: it is trivial on the image of $\mathbb{Q}^{\times}$ under the diagonal embedding, it is continuous, and it is of finite order. Second, $\eta$ admits the modulus $\mathrm{span}\{q^b\} \subseteq \mathcal{O}_{\mathbb{Q}}$, i.e. $\eta(u) = 1$ for every idele unit $u$ whose infinite component is $1$ and whose component at each finite place $v$ has valuation $1$ and satisfies $v(u_v - 1) \le \exp(-m_v)$, where $m_v$ is the multiplicity of $v$ in that ideal. Third, $\eta$ is unitary: $\lVert \eta(x)\rVert = 1$ for all ideles $x$. Fourth, for every prime $\ell \neq q$, the value of $\eta$ at the idele which is a uniformiser of the completion at the place of $\mathcal{O}_{\mathbb{Q}}$ corresponding to $\ell$ and $1$ at all other places (finite and infinite) equals $\chi_0$ of the class of $\ell$, a unit modulo $q^b$ since $\ell$ and $q$ are distinct primes. Fifth, for every $u \in \mathbb{Z}_q^{\times}$, the value of $\eta$ at the idele with component $u$ at the place corresponding to $q$ (transported along the isomorphism $\mathbb{Q}_q \cong$ the completion there) and $1$ elsewhere equals $\chi_0(u \bmod q^b)^{-1}$. Sixth, for every $x \in \mathbb{Q}_q^{\times}$ with $x = q$, the value of $\eta$ at the idele with component $x$ at that place and $1$ elsewhere is $1$.
--
--   This is the passage from a Dirichlet character of prime-power modulus $q^b$ to the associated finite-order idele class character of $\mathbb{Q}$, with the local component at $q$ itself prescribed on the local units and normalised to be trivial on the uniformiser $q$, rather than only the values at the places away from the modulus. In this form it supplies the twisting characters used when adjusting the ramification of the local component at $q$ of the automorphic representation attached to a newform, and it is cited in the construction of admissible twists and of quadratic twists reducing the exponent of the conductor at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
    (q : ℕ) [Fact q.Prime] (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ η ∧
      HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)) ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers ℚ) ℚ η ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q),
        (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) =
          χ₀ (ZMod.unitOfCoprime ℓ (((Nat.coprime_primes hℓ (Fact.out : q.Prime)).mpr hℓq).pow_right b))) ∧
      (∀ u : ℤ_[q]ˣ,
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) =
          (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) ∧
      (∀ x : ℚ_[q]ˣ, (x : ℚ_[q]) = q →
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom x))) = 1) := by sorry
