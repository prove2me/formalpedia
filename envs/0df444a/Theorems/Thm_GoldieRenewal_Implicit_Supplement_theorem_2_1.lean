-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_theorem_2_1
-- name    : GoldieRenewal.Implicit.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:14:37.190848+00:00
-- url     : https://prove2.me/theorems/8ff30405-62b4-4d31-b947-fff0d299cc37
-- title:
--   Theorem 2.1 (Letac's principle) — an a.s. limit Z of Ψ₁ ∘ ⋯ ∘ Ψ_n(t) not depending on t has the unique law solving (2.1); W_n(t) converges to it in law
-- statement:
--   Let $\Psi:\mathbb R\times\Omega\to\mathbb R$ be jointly measurable with continuous paths: for each $\omega$, $t\mapsto\Psi(t,\omega)$ is continuous. Let $\Psi_1,\Psi_2,\dots$ be independent copies of $\Psi$, and $Z_n(t):=\Psi_1\circ\cdots\circ\Psi_n(t)$. Suppose that there is a random variable $Z$ with
--   $$
--   Z_n(t)\to Z\quad\text{a.s.}\quad(n\to\infty)\qquad\text{for every } t\in\mathbb R .
--   $$
--   Then
--
--   1. the law of $Z$ is a law for $R$ satisfying (2.1), $R\overset{L}{=}\Psi\circ R$ with $\Psi$ and $R$ independent;
--   2. it is the unique such law;
--   3. whatever the initial $t$, the forward iterates $W_n(t):=\Psi_n\circ\cdots\circ\Psi_1(t)$ converge in law to it.
--
--   The paper quotes this from Letac (1986). Propositions 5.1, 6.1 and 8.1 are applications, and they supply the existence and uniqueness of the laws in Theorems 5.2, 6.2 and 8.2.
--
--   **Formalization Note** The copies live on their own probability space $(\Omega',P')$; they are independent as random elements of $\mathbb R^{\mathbb R}$ (product $\sigma$-algebra), each has the law of $\Psi$, and each is jointly measurable with continuous paths. $Z$ is an a.e. limit of measurable maps, hence a.e.-measurable, so its law is well defined. "A law $\rho$ for $R$ satisfying (2.1)" is tested on every realization: whenever a copy $\Phi$ of $\Psi$ (jointly measurable, continuous paths, the law of $\Psi$) and an independent $R$ live on one probability space, $R\sim\rho$ implies $\Phi(R)\sim\rho$; uniqueness says that $\Phi(R)\overset{L}{=}R$ forces $R\sim$ law of $Z$. Convergence in law is convergence of $E f(W_n(t))$ for every bounded continuous $f$.
--
--   Differences from the source:
--
--   - reading: independent copies Ψ₁, Ψ₂, … of Ψ on a suitably enlarged probability space → a sequence on a separate probability space, independent, each with the law of Ψ and each jointly measurable with continuous paths; reason: continuity of paths is not determined by the law on the product σ-algebra; copies built from Ψ have it, and the theorem's hypothesis on Ψ is meant for them
--   - reading: Z := lim Z_n(t) exists a.s. and does not depend on t → one Z with Z_n(t) → Z a.s. for every t; reason: this is the literal content of the hypothesis; the null set may depend on t
--   - reading: a law for R satisfying (2.1), and the unique such law → for every probability space carrying a copy Φ of Ψ with continuous paths and an independent R: R ∼ law Z ⇒ Φ(R) ∼ law Z, and Φ(R) =_L R ⇒ R ∼ law Z; reason: (2.1) is a statement about the law of Ψ; the original (Ω, P, Ψ) is one such space, so this covers the paper's R
--   - encoding: W_n(t) has this law as its limit law → E f(W_n(t)) → E f(Z) for every bounded continuous f; reason: the definition of convergence in law
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 128, Theorem 2.1 (Letac 1986)

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Letac

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

universe u

/-- **Theorem 2.1, Letac's principle** (Goldie, *Implicit renewal theory and tails of solutions of
random equations*, Ann. Appl. Probab. 1(1) (1991), p. 128; Letac (1986)). Let `Ψ : ℝ × Ω → ℝ` be
jointly measurable with continuous paths, and let `Ψ₁, Ψ₂, …` be independent copies of `Ψ` (on a
probability space `(Ω', P')`). Suppose `Z := lim_{n→∞} Z_n(t)`, `Z_n(t) := Ψ₁ ∘ ⋯ ∘ Ψ_n(t)`, exists
a.s. and does not depend on `t`. Then

1. the law of `Z` is a law for `R` satisfying (2.1), `R =_L Ψ ∘ R` with `Ψ` and `R` independent;
2. it is the unique such law;
3. for every initial `t`, `W_n(t) := Ψ_n ∘ ⋯ ∘ Ψ₁(t)` converges in law to it.

**Formalization Note** The copies are a sequence `Ψs` on `(Ω', P')`, mutually independent as random
elements of `ℝ → ℝ` (product σ-algebra), each with the law of `Ψ`, each jointly measurable with
continuous paths. "`Z` exists a.s. and does not depend on `t`" is: for every `t`, `Z_n(t) → Z`
`P'`-a.s. `Z` is then an a.e. limit of measurable maps, hence a.e.-measurable, so `P'.map Z` is its
law. "A law `ρ` for `R` satisfying (2.1)" is tested on every realization: whenever `R` with law `ρ`
and a copy `Φ` of `Ψ` (jointly measurable, continuous paths, the law of `Ψ`) live on a probability
space with `R` independent of `Φ`, `Φ(R)` has law `ρ`; uniqueness says every `R` independent of such a
`Φ` with `Φ(R) =_L R` has the law of `Z`. Convergence in law is convergence of `E f(W_n(t))` for every
bounded continuous `f`. -/
theorem theorem_2_1 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Ψ : ℝ → Ω → ℝ) (hΨ : Measurable (fun p : ℝ × Ω => Ψ p.1 p.2))
    (hΨ_cont : ∀ ω, Continuous (fun t => Ψ t ω))
    {Ω' : Type u} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ψs : ℕ → ℝ → Ω' → ℝ) (hΨs : ∀ n, Measurable (fun p : ℝ × Ω' => Ψs n p.1 p.2))
    (hΨs_cont : ∀ n ω, Continuous (fun t => Ψs n t ω))
    (hΨs_indep : iIndepFun (fun n ω => fun t => Ψs n t ω) P')
    (hΨs_law : ∀ n, IdentDistrib (fun ω => fun t => Ψs n t ω) (fun ω => fun t => Ψ t ω) P' P)
    (Z : Ω' → ℝ)
    (hZ : ∀ t : ℝ, ∀ᵐ ω ∂P', Tendsto (fun n => backwardIter Ψs n t ω) atTop (𝓝 (Z ω))) :
    -- 1. the law of `Z` solves (2.1)
    (∀ (Ω₂ : Type u) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (Φ : ℝ → Ω₂ → ℝ) (R : Ω₂ → ℝ),
        Measurable (fun p : ℝ × Ω₂ => Φ p.1 p.2) → (∀ ω, Continuous (fun t => Φ t ω)) →
        IdentDistrib (fun ω => fun t => Φ t ω) (fun ω => fun t => Ψ t ω) P₂ P →
        Measurable R → IndepFun R (fun ω => fun t => Φ t ω) P₂ →
        P₂.map R = P'.map Z → P₂.map (fun ω => Φ (R ω) ω) = P₂.map R) ∧
    -- 2. and is the unique such law
    (∀ (Ω₂ : Type u) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (Φ : ℝ → Ω₂ → ℝ) (R : Ω₂ → ℝ),
        Measurable (fun p : ℝ × Ω₂ => Φ p.1 p.2) → (∀ ω, Continuous (fun t => Φ t ω)) →
        IdentDistrib (fun ω => fun t => Φ t ω) (fun ω => fun t => Ψ t ω) P₂ P →
        Measurable R → IndepFun R (fun ω => fun t => Φ t ω) P₂ →
        P₂.map (fun ω => Φ (R ω) ω) = P₂.map R → P₂.map R = P'.map Z) ∧
    -- 3. the forward iterates converge in law to it, whatever the initial `t`
    (∀ (t : ℝ) (f : ℝ →ᵇ ℝ),
        Tendsto (fun n => ∫ ω, f (forwardIter Ψs n t ω) ∂P') atTop (𝓝 (∫ ω, f (Z ω) ∂P'))) := by sorry

end GoldieRenewal.Implicit.Supplement
