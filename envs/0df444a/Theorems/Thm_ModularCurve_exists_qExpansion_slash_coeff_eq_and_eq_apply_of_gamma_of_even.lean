-- Prove2me | Theorems.Thm_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
-- name    : ModularCurve.exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/849d2c3e-40d4-5e3f-8294-6a0a84801c16
-- title:
--   Shimura reciprocity at the cusps, even weight, level Γ(N)
-- statement:
--   Let $N$ be a nonzero natural number and $k$ an even integer, and let $F$ be a modular form of weight $k$ for the image of the principal congruence subgroup $\Gamma(N) \le \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$. Assume that every coefficient of the width-$N$ $q$-expansion of $F$ at $\infty$, in the parameter $q_N = e^{2\pi i \tau / N}$, is rational, i.e. for each $n$ the $n$-th coefficient is the image of some $r \in \mathbb{Q}$. Let $K$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{C}$ equal to $\mathbb{Q}$ adjoined the single element $\zeta_N = e^{2\pi i/N}$, let $s$ be a natural number coprime to $N$, and let $\varphi\colon K \to \mathbb{C}$ be a ring homomorphism such that any element of $K$ whose image in $\mathbb{C}$ is $\zeta_N$ is sent by $\varphi$ to $\zeta_N^{\,s}$. Let $\gamma, \gamma' \in \mathrm{SL}_2(\mathbb{Z})$ satisfy, after reduction of their entries modulo $N$, the relation $\mathrm{diag}(1,s)\,\gamma' = \gamma\,\mathrm{diag}(1,s)$ in $\mathrm{M}_2(\mathbb{Z}/N\mathbb{Z})$. Then for each natural number $n$ there exists $z \in K$ whose image in $\mathbb{C}$ is the $n$-th coefficient of the width-$N$ $q$-expansion of the weight-$k$ slash $F \mid_k \gamma$, and such that the $n$-th coefficient of the width-$N$ $q$-expansion of $F \mid_k \gamma'$ equals $\varphi(z)$.
--
--   This is Shimura's reciprocity law at the cusps in even weight for level $\Gamma(N)$: the expansion of $F$ read through $\gamma$ has coefficients in $\mathbb{Q}(\zeta_N)$, and applying $\zeta_N \mapsto \zeta_N^{\,s}$ coefficientwise produces the expansion read through any $\gamma'$ conjugate to $\gamma$ by $\mathrm{diag}(1,s)$ modulo $N$. It is obtained from the corresponding statement for $\Gamma(N)$-invariant functions with bounded behaviour at the cusps after multiplication by a power of the discriminant, and it feeds the rationality statements for slashed forms at full level used in the analysis of expansions along $\Gamma_0$-type subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_qExpansion_slash_coeff_eq_and_eq_apply_of_gamma_of_even
    (N : ℕ) [NeZero N] {k : ℤ} (hk : Even k)
    (F : ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion N F).coeff n = (r : ℂ))
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N) (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (γ γ' : SL(2, ℤ))
    (hγγ' : !![(1 : ZMod N), 0; 0, (s : ZMod N)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * !![(1 : ZMod N), 0; 0, (s : ZMod N)])
    (n : ℕ) :
    ∃ z : ↥K, (z : ℂ) = (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n ∧
      (UpperHalfPlane.qExpansion N ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ')).coeff n = φ z := by sorry
