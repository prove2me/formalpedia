-- Prove2me | Theorems.Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
-- name    : ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/8b5c88d9-30d0-56f2-a436-45a323f6aeea
-- title:
--   Integral Eisenstein family on Γ₁(M) permuted by Γ₀(M)
-- statement:
--   Let $M$ be a nonzero natural number and let $k$ be a natural number with $3 \le k$. Then there is a family $G$, indexed by the residue classes $c \in \mathbb{Z}/M$, of modular forms of weight $k$ for the congruence subgroup $\Gamma_1(M)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, with the following two properties. First, for every $c \neq 0$ the form $G(c)$ has integral $q$-expansion with prescribed coefficients: the power series over $\mathbb{Z}$ whose $n$-th coefficient is $$\sum_{\substack{m \mid n,\ m>0 \\ n/m \equiv c}} m^{k-1} + (-1)^k \sum_{\substack{m \mid n,\ m>0 \\ n/m \equiv -c}} m^{k-1},$$ the congruences being in $\mathbb{Z}/M$, becomes, after applying the ring homomorphism $\mathbb{Z} \to \mathbb{C}$ coefficientwise, exactly the $q$-expansion of $G(c)$ of width $1$, i.e. in $q = e^{2\pi i \tau}$. (For $n = 0$ the set of divisors is empty, so the constant term is $0$.) Second, for every $c \in \mathbb{Z}/M$ and every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(M)$, the weight-$k$ slash of the function $\mathbb{H} \to \mathbb{C}$ underlying $G(c)$ by $\gamma$ equals the function underlying $G(c \cdot a)$, where $a$ is the reduction modulo $M$ of the upper-left entry $\gamma_{00}$. Nothing is asserted about the $q$-expansion of $G(0)$.
--
--   This is the classical family of weight-$k$ Eisenstein series of level $\Gamma_1(M)$ attached to residue classes modulo $M$, normalised so that the Fourier coefficients are the divisor sums above, together with the permutation action of the diamond operators coming from $\Gamma_0(M)$. It supplies the Eisenstein part of integral bases of $q$-expansions used in the construction of bases of cusp forms with integral coefficients and in the treatment of diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq (M : ℕ) [NeZero M]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ G : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ c : ZMod M, c ≠ 0 →
        ModularCurve.IsIntegralQExp (G c)
          (PowerSeries.mk fun n : ℕ =>
            (∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = c, (m : ℤ) ^ (k - 1)) +
              (-1) ^ k * ∑ m ∈ n.divisors with ((n / m : ℕ) : ZMod M) = -c, (m : ℤ) ^ (k - 1))) ∧
      ∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        ((⇑(G c) : UpperHalfPlane → ℂ) ∣[(k : ℤ)] γ) =
          (⇑(G (c * ((γ 0 0 : ℤ) : ZMod M))) : UpperHalfPlane → ℂ) := by sorry
