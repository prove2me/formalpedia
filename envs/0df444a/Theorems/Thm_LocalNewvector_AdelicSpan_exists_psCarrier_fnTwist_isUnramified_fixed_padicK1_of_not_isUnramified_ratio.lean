-- Prove2me | Theorems.Thm_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
-- name    : LocalNewvector.AdelicSpan.exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/7dfff7c1-0261-5747-b93c-a76bd8fabccb
-- title:
--   Twisting away ramification of μ₁ in a principal series
-- statement:
--   Let $q$ be a prime and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$. Assume $\Phi(x\cdot k)=\Phi(x)$ for every $k$ in the congruence subgroup [`LocalNewvector.padicK1 q n₀`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) $=$ `congruenceK1 (q : ℤ_[q]) n₀` of $\mathrm{GL}_2(\mathbb{Q}_q)$, embedded adelically by [`AdelicDock.padicToAdelic`](def/AdelicDock_LocalEmbedding.html#L254), for some $n_0$, and $\Phi(x\cdot z(u))=\Phi(x)$ for every $u\in\mathbb{Z}_q^{\times}$, where $z(u)=$ [`LocalNewvector.centralGL q u`](def/LocalNewvector_ConductorDatum.html#L64) is the central scalar matrix. Let $\mu_1,\mu_2:\mathbb{Q}_q^{\times}\to\mathbb{C}^{\times}$ be characters, and let $f$ be a nonzero $\mathbb{C}$-linear map from the module [`LocalNewvector.AdelicSpan Φ`](def/LocalNewvector_AdelicSpanCarrier.html#L82) to the principal-series carrier [`LocalNewvector.PSCarrier q μ₁ μ₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173) satisfying $f(x\cdot v)=x\cdot f(v)$ for all $x\in\mathrm{GL}_2(\mathbb{Q}_q)$. Assume $\mu_1^{-1}\mu_2$ is not unramified, i.e. some $u$ with $\|u\|=1$ has $(\mu_1^{-1}\mu_2)(u)\neq 1$. Let $b\in\mathbb{N}$ and $\chi_0:(\mathbb{Z}/q^b)^{\times}\to\mathbb{C}^{\times}$ with $\mu_1(u)=\chi_0(u\bmod q^b)$ for all $u\in\mathbb{Z}_q^{\times}$, and let $\eta$ be a character of the idele units of $\mathbb{Q}$ whose value on the idele with $q$-component $u\in\mathbb{Z}_q^{\times}$ and trivial components elsewhere is $\chi_0(u\bmod q^b)^{-1}$. Then there are characters $\nu_1,\nu_2$ of $\mathbb{Q}_q^{\times}$, a nonzero $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map $f'$ from [`LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)`](def/LocalNewvector_AdelicSpanCarrier.html#L82), the span attached to the twisted function $g\mapsto \eta(\det g)\,\Phi(g)$, to [`LocalNewvector.PSCarrier q ν₁ ν₂`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173), a natural number $a$, and an element $y$ of that twisted span, such that $\nu_1$ is unramified (trivial on all $u$ with $\|u\|=1$), $\mu_1^{-1}\mu_2$ has conductor exponent $a$ in the sense of [`LocalNewvector.HasCharConductor`](def/LocalNewvector_CharConductor.html#L92) (trivial on `higherUnits q a` and nontrivial on `higherUnits q m` for every $m<a$), $y$ lies in the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121) of the twisted span, $y\neq 0$, $y$ is fixed by [`LocalNewvector.padicK1 q a`](def/LocalNewvector_CongruenceSubgroupK1.html#L161), and $z(u)\cdot y=\mu_1(u)^{-2}\,y$ for every $u\in\mathbb{Z}_q^{\times}$.
--
--   This is the local twisting step which replaces a principal series $B(\mu_1,\mu_2)$ with ramified first character by one in which the first character is unramified, while producing a vector fixed by $K_1(q^a)$ with $a$ the conductor exponent of $\mu_1^{-1}\mu_2$ and with the prescribed central character. It is used in the construction of a primitive form from a newform whose local principal-series ratio at $q$ is ramified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalNewvector_AdelicSpan_exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio.lean

import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.NumberTheory.Padics.RingHoms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LocalNewvector.AdelicSpan.exists_psCarrier_fnTwist_isUnramified_fixed_padicK1_of_not_isUnramified_ratio
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (q : ℕ) [Fact q.Prime]
    (n₀ : ℕ) (hΦK : ∀ k ∈ LocalNewvector.padicK1 q n₀, ∀ x, Φ (x * AdelicDock.padicToAdelic q k) = Φ x)
    (hΦZ : ∀ (u : ℤ_[q]ˣ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Φ (x * AdelicDock.padicToAdelic q
        (LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u))) = Φ x)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : ¬ LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂))
    (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ)
    (hχ₀compat : ∀ u : ℤ_[q]ˣ,
      μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) =
        χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))
    (η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ)
    (hηu : ∀ u : ℤ_[q]ˣ,
      η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u))))
        = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) :
    ∃ (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ)
      (f' : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ) →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
      (a : ℕ) (y : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
      (∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)),
          f' (x • v) = x • f' v) ∧
      f' ≠ 0 ∧ LocalNewvector.IsUnramified q ν₁ ∧
      LocalNewvector.HasCharConductor q (μ₁⁻¹ * μ₂) a ∧
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] =>
          x • LocalNewvector.AdelicSpan.self (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a)
        (LocalNewvector.AdelicSpan (AutomorphicForm.fnTwist ℚ η Φ)) ∧
      ∀ u : ℤ_[q]ˣ,
        LocalNewvector.centralGL q (Units.map PadicInt.Coe.ringHom.toMonoidHom u) • y =
          ((μ₁ (Units.map PadicInt.Coe.ringHom.toMonoidHom u) : ℂ) ^ 2)⁻¹ • y := by sorry
