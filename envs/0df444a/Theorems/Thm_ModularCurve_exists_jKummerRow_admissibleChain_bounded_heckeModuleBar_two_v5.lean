-- Prove2me | Theorems.Thm_ModularCurve_exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5
-- name    : ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/e865abaa-f45a-582a-9365-f587fbc1e25c
-- title:
--   Localised Kummer package at 2 with bounded admissible chains
-- statement:
--   Let $p$ be a prime, assume the operators `heckeOperatorBar` at all rational primes commute pairwise on $J =$ `JZero p`, the degree-zero divisor class group of the modular function field of level $p$ base-changed to $\overline{\mathbb Q}$, and assume $2$ divides $|p-1|/\gcd(p-1,12)$. Then there are, for every $m$, a Kummer row $R_m$ at level $2^m$ over the localised module `eisensteinQuotientRationalLocalized p 2` — that is, abelian groups $M_0^{(m)}, H^1_{\mathrm{tors}}(m), H^1(m)$, an injective map $M_0^{(m)} \to$ `eisensteinQuotientRationalLocalized p 2` with finite-index image, a map $\delta$ from $M_0^{(m)}$ to $H^1_{\mathrm{tors}}(m)$ whose kernel is $2^m M_0^{(m)}$, exact at $H^1_{\mathrm{tors}}(m)$ with a map `push` into $H^1(m)$ whose image is the $2^m$-torsion of $H^1(m)$ — with every $H^1_{\mathrm{tors}}(m)$ finite; open actions $\Phi_m$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (group homomorphisms into the additive automorphisms with open kernel) on the $2^m$-torsion part `eisensteinPrimaryTorsionBar p 2 m` that agree with the natural Galois action on $J$; admissible chains $c_m$ for $\Phi_m$ (filtrations by subgroups from $\bot$ to $\top$ with successive quotients of order $2$, each step tagged as trivial or cyclotomic accordingly); and functions $h^0, \delta, h^1 : \mathbb N \to \mathbb N$ such that $\#H^1_{\mathrm{tors}}(m) \le 2^{h^1(m)}$, $h^1(m) + \alpha(c_m) \le h^0(m) + \delta(m)$ where $\alpha$ counts the steps tagged trivial, there exist $g \in \mathbb N$ and $C \in \mathbb Z$ with $\delta(m) \le mg + C$ and $mg \le \alpha(c_m) + C$ for all $m$, and $h^0$ is bounded.
--
--   This assembles, at the prime $2$ and after localisation at the $2$-Eisenstein maximal ideal, the numerical package of Mazur's study of the Eisenstein ideal: a Kummer-theoretic row over the Hecke span of the rational points of the Eisenstein quotient, an admissible filtration of the Eisenstein-primary $2^m$-torsion of $J_0(p)$, and the inequalities relating the invariants $h^0$, $h^1$, $\delta$ and $\alpha$. It feeds the companion statement [`ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_v5`](thm.html#ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve MazurAdmissible

theorem ModularCurve.exists_jKummerRow_admissibleChain_bounded_heckeModuleBar_two_v5 (p : ℕ)
    [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (h2n : 2 ∣ ((p : ℤ) - 1).natAbs / ((p : ℤ) - 1).gcd 12) :
    ∃ R : ∀ m : ℕ, JKummerRow (2 : ℕ) m (eisensteinQuotientRationalLocalized p 2),
      (∀ m : ℕ, letI := (R m).instH1Jtors; Finite (R m).H1Jtors) ∧
      ∃ Φ : ∀ m : ℕ, OpenAction ↥(eisensteinPrimaryTorsionBar p 2 m),
        (∀ m : ℕ, ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
            (x : ↥(eisensteinPrimaryTorsionBar p 2 m)),
            ((Φ m).φ σ x : JZero p) = σ • (x : JZero p)) ∧
        ∃ c : ∀ m : ℕ, AdmissibleChain (2 : ℕ) (Φ m),
          ∃ h0 δ h1 : ℕ → ℕ,
            (∀ m : ℕ,
              letI := (R m).instH1Jtors
              Nat.card (R m).H1Jtors ≤ (2 : ℕ) ^ h1 m) ∧
            (∀ m : ℕ, (h1 m : ℤ) + (filtAlpha (c m) : ℤ) ≤ (h0 m : ℤ) + (δ m : ℤ)) ∧
            (∃ g : ℕ, ∃ C : ℤ, ∀ m : ℕ,
              (δ m : ℤ) ≤ (m : ℤ) * (g : ℤ) + C ∧
                (m : ℤ) * (g : ℤ) ≤ (filtAlpha (c m) : ℤ) + C) ∧
            (∃ H₀ : ℕ, ∀ m : ℕ, h0 m ≤ H₀) := by sorry
