-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_1
-- name    : HopfieldPSpin.Shattering.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:42.781298+00:00
-- url     : https://prove2.me/theorems/34b75bea-fbc3-4043-b95a-3e15294dd067
-- title:
--   Lemma 4.1 — covariance structure of $X_k$ and $H_n$: $Q_{n,p}$, $v_{n,p}$, symmetry, $0\le D_n\le2$
-- statement:
--   Fix $p\ge3$, $n\ge p$, $M\ge1$ and either pattern law. For all $k$ and $\sigma,\tau\in\Sigma_n$: $X_k(\sigma)$ and $H_n(\sigma)$ have finite second moments, $\mathbb EX_k(\sigma)=0$, $\mathbb EX_k(\sigma)X_k(\tau)=Q_{n,p}(\sigma,\tau)$, $\mathbb EH_n(\sigma)H_n(\tau)=nQ_{n,p}(\sigma,\tau)$ and $\operatorname{Var}H_n(\sigma)=nv_{n,p}$. With $q=R_n(\sigma,\tau)$,
--   $$|Q_{n,p}(\sigma,\tau)-q^p|\le1-v_{n,p}\le\frac1n\binom p2 .$$
--   $Q_{n,p}$ depends only on $q$; $Q_{n,p}(-q)=(-1)^pQ_{n,p}(q)$ and $H_n(-\sigma)=(-1)^pH_n(\sigma)$; $|Q_{n,p}|\le v_{n,p}$; and $D_n=v_{n,p}+Q_{n,p}$ satisfies $0\le D_n\le2$, $D_n=\tfrac12\operatorname{Var}(X_k(\sigma)+X_k(\tau))=\tfrac1{2n}\operatorname{Var}(H_n(\sigma)+H_n(\tau))$, and $D_n=0$ for odd $p$ when $q=-1$.
--
--   This is the covariance computation that matches the Hopfield model to the pure $p$-spin model up to $O(1)$ corrections.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: $Q_{n,p}$ depends only on $q$; $Q_{n,p}(-q)=(-1)^pQ_{n,p}(q)$ for every attainable $q$ → equal overlaps give equal $Q_{n,p}$; $Q_{n,p}(\sigma,-\tau)=(-1)^pQ_{n,p}(\sigma,\tau)$; reason: the attainable $q$ are the overlaps $R_n(\sigma,\tau)$ and $R_n(\sigma,-\tau)=-R_n(\sigma,\tau)$
--   - encoding: $D_n(q)$ vanishes for odd $p$ when $q=-1$ → `Odd p → overlap σ τ = -1 → covD n p σ τ = 0`; reason: same statement
--   - encoding: expectations and variances of $X_k$, $H_n$ (finite, implicitly) → explicit `MemLp … 2` clauses for $X_k(\sigma)$ and $H_n(\sigma)$, Bochner integrals and Mathlib `variance`; reason: makes every integral in the statement a genuine one (no junk value for non-integrable functions)
--   - encoding: patterns $\eta^1,\dots,\eta^M$ (so $M\ge1$) and the standing $p\ge3$, $n\ge p$ → hypotheses `0 < M`, `3 ≤ p`, `p ≤ n`; reason: standing assumptions of §2 and §4.1 written as binders
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 15 (PDF 17), Lemma 4.1, (4.3)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

open MeasureTheory ProbabilityTheory

namespace HopfieldPSpin.Shattering

/-- Lemma 4.1 (p. 15): covariance structure of the one-pattern fields and of the Hamiltonian,
for either pattern law, under the standing assumptions `p ≥ 3`, `n ≥ p` and `M ≥ 1`. -/
theorem lemma_4_1 (n M p : ℕ) (hp : 3 ≤ p) (hn : p ≤ n) (hM : 0 < M) (law : PatternLaw) :
    (∀ (k : Fin M) (σ : Config n), MemLp (fun η => patternField n M p η k σ) 2 (disorderLaw n M law)) ∧
    (∀ σ : Config n, MemLp (fun η => hamiltonian n M p η σ) 2 (disorderLaw n M law)) ∧
    (∀ (k : Fin M) (σ : Config n), ∫ η, patternField n M p η k σ ∂(disorderLaw n M law) = 0) ∧
    (∀ (k : Fin M) (σ τ : Config n),
      ∫ η, patternField n M p η k σ * patternField n M p η k τ ∂(disorderLaw n M law) =
        covQ n p σ τ) ∧
    (∀ σ τ : Config n,
      ∫ η, hamiltonian n M p η σ * hamiltonian n M p η τ ∂(disorderLaw n M law) =
        n * covQ n p σ τ) ∧
    (∀ σ : Config n, variance (fun η => hamiltonian n M p η σ) (disorderLaw n M law) = n * covV n p) ∧
    (∀ σ τ : Config n, |covQ n p σ τ - overlap σ τ ^ p| ≤ 1 - covV n p ∧
      1 - covV n p ≤ (1 / (n : ℝ)) * (p.choose 2 : ℝ)) ∧
    (∀ σ τ σ' τ' : Config n, overlap σ τ = overlap σ' τ' → covQ n p σ τ = covQ n p σ' τ') ∧
    (∀ σ τ : Config n, covQ n p σ (-τ) = (-1) ^ p * covQ n p σ τ) ∧
    (∀ (η : Fin M → Fin n → ℝ) (σ : Config n), hamiltonian n M p η (-σ) = (-1) ^ p * hamiltonian n M p η σ) ∧
    (∀ σ τ : Config n, |covQ n p σ τ| ≤ covV n p) ∧
    (∀ σ τ : Config n, 0 ≤ covD n p σ τ ∧ covD n p σ τ ≤ 2) ∧
    (∀ (k : Fin M) (σ τ : Config n), covD n p σ τ =
      (1 / 2) * variance (fun η => patternField n M p η k σ + patternField n M p η k τ) (disorderLaw n M law)) ∧
    (∀ σ τ : Config n, covD n p σ τ =
      (1 / (2 * (n : ℝ))) * variance (fun η => hamiltonian n M p η σ + hamiltonian n M p η τ) (disorderLaw n M law)) ∧
    (Odd p → ∀ σ τ : Config n, overlap σ τ = -1 → covD n p σ τ = 0) := by sorry

end HopfieldPSpin.Shattering
