-- Prove2me | Theorems.Thm_ModularForm_exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd
-- name    : ModularForm.exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/c4d14b8e-f191-549c-8ac9-25b171846e32
-- title:
--   Mod p q-expansion principle for Γ₀(M)-translates
-- statement:
--   Let $M \ge 1$ be a natural number, let $p$ be a prime with $p \nmid M$, and let $k$ be an integer. Let $f$ be a modular form of weight $k$ for the subgroup of $\mathrm{GL}(2,\mathbb{R})$ obtained from the congruence subgroup $\Gamma_1(M)$. Assume two integrality hypotheses on the $q$-expansion coefficients at width $1$, where [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) of a function $\mathbb{H} \to \mathbb{C}$ at $n$ denotes the $n$-th coefficient of its $q$-expansion of width $1$: first, for every $\gamma \in \Gamma_0(M) \subseteq \mathrm{SL}(2,\mathbb{Z})$ and every $n \in \mathbb{N}$, the $n$-th $q$-coefficient of the weight-$k$ slash translate $f \mid[k]\,\gamma$ lies in the image of $\mathbb{Z} \to \mathbb{C}$; second, for every $n \in \mathbb{N}$ the $n$-th $q$-coefficient of $f$ itself is of the form $p\,m$ with $m \in \mathbb{Z}$. Then for each fixed $\gamma \in \Gamma_0(M)$ and each $n \in \mathbb{N}$ there is an integer $m$ with the $n$-th $q$-coefficient of $f \mid[k]\,\gamma$ equal to $p\,m$; that is, divisibility by $p$ of the expansion at $\infty$ passes to all $\Gamma_0(M)$-translates.
--
--   This is the form of Katz's $q$-expansion principle modulo a prime $p \nmid M$ used in the project: integrality of all $\Gamma_0(M)$-translates plus divisibility by $p$ at the single cusp $\infty$ forces divisibility by $p$ at the translated cusps. It feeds the construction comparing regular differentials on the modular curve with integral $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm MatrixGroups

theorem ModularForm.exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
      ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) n ∈ Set.range ((↑) : ℤ → ℂ))
    (hp : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑f : UpperHalfPlane → ℂ) n = (p : ℂ) * m)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (n : ℕ) :
    ∃ m : ℤ, ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) n = (p : ℂ) * m := by sorry
