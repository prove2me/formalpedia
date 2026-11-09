-- Prove2me | Theorems.Thm_GoodQLTC_theorem_4_12
-- name    : GoodQLTC.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:04.724645+00:00
-- url     : https://prove2.me/theorems/8e29dd51-949e-4714-8ed3-e843fcbdca9c
-- title:
--   Theorem 4.12: the abstract construction
-- statement:
--   For every integer $t\ge4$, $0<\rho\le1$ and $\tau\ge1$ there is $\lambda_0=\lambda_0(t,\rho,\tau)\in(0,1)$ such that: for integers $2\le k\le t-2$, $s\ge1$, $2\le n_1\le\dots\le n_t$, $0<m_{i,b}<n_i$ with $n_t/n_1\le\tau$, there are constants $\delta,\sigma>0$ and $w\in\mathbb N_{\ge1}$, depending only on $t,k,s,\{n_i\},\{m_{i,b}\},\rho,\tau$, such that for every $0\le\lambda\le\lambda_0$ and every family $\{(X_\nu,\mathcal F_\nu)\}$ satisfying (1)–(3) of the theorem (regular $\lambda$-expanding complexes with $|X_\nu(0)|\to\infty$; $\mathbb F_{2^s}$-cosheaves with compatible base codes; universally $\rho$-product-expanding local codes and duals), the codes $Q_\nu$ of Equation (4.5) satisfy, for every $\nu$:
--   1. $K(Q_\nu)/N_\nu\ge\Gamma_k(J')/\mathrm{sym}_{t-k}(S_1,\dots,S_t)$ for every $J'\subseteq[t]$ with $|J'|=k$;
--   2. $d(Q_\nu)\ge\delta N_\nu$;
--   3. $Q_\nu$ is $w$-locally testable with soundness $\sigma$;
--   4. at most $w$ checks are incident to each qubit;
--
--   and $N_\nu\to\infty$.
--
--   Differences from the source:
--   - reading: Equation (4.5) gives a family of CSS codes {Q_ν} (part of a ⟦N_ν, r, δ⟧ family) → the conclusion includes N_ν → ∞; reason: proved on p.33 (N_ν = sV_νD_{[t]}sym_{t−k}(S) → ∞) and used by Theorem 4.14
--   - generalization: universal product expansion over every field extension E/F → the hypothesis quantifies over extensions E in one universe u (a parameter of the theorem); reason: Lean has no type of all fields; the paper's hypothesis (all extensions) implies the one-universe hypothesis, so the statement specializes to the source's
--   - encoding: families indexed by ν ≥ 1 → families indexed by ν ∈ ℕ; reason: index shift; same instances
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
--   - encoding: an ordered F_2-basis β of F → an additive isomorphism F ≃ F_2^s; reason: the coordinate map of an ordered basis; every additive isomorphism of F_2-spaces is F_2-linear
--   - encoding: d(Q_ν) ≥ δN_ν with d ∈ ℕ ∪ {∞} → ENNReal.ofReal(δN_ν) ≤ d(Q_ν); reason: same inequality for finite and infinite d
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 4.12, p.19 (PDF p.22); proof p.33

import Mathlib
import Definitions.Def_GoodQLTC_logicalQubits
import Definitions.Def_GoodQLTC_cssDist
import Definitions.Def_GoodQLTC_IsLocallyTestable
import Definitions.Def_GoodQLTC_cssHX
import Definitions.Def_GoodQLTC_rateGamma
import Definitions.Def_GoodQLTC_FamilyHyp

namespace GoodQLTC

universe u

/-- **Theorem 4.12** (the abstract construction), Gay–Jeronimo, arXiv:2609.20780 (held version),
p.19: for every integer `t ≥ 4`, `0 < ρ ≤ 1` and `τ ≥ 1` there is `λ_0 = λ_0(t, ρ, τ) ∈ (0, 1)`
with the following property. Fix integers `2 ≤ k ≤ t − 2`, `s ≥ 1`, `2 ≤ n_1 ≤ ⋯ ≤ n_t` and
`0 < m_{i,b} < n_i`; suppose `n_t/n_1 ≤ τ` and `0 ≤ λ ≤ λ_0`; let `{(X_ν, F_ν)}` satisfy (1)–(3)
(`FamilyHyp`). Then Equation (4.5) gives CSS codes `Q_ν` with `K(Q_ν)/N_ν ≥ Γ_k(J')/sym_{t−k}(S)`
for every `J' ⊆ [t]` with `|J'| = k`; moreover there are `δ, σ > 0` and `w ∈ ℕ_{≥1}`, depending
only on `t, k, s, {n_i}, {m_{i,b}}, ρ, τ`, such that each `Q_ν` has distance at least `δ N_ν`, is
`w`-locally testable with soundness `σ`, and has at most `w` checks incident to each qubit.

**Formalization Note.** Quantifier order: `λ_0` after `t, ρ, τ`; `δ, σ, w` after
`t, k, s, n, m` (and `ρ, τ`), before `λ`, the field `F` (any field with `2^s` elements), the
family, and the `F_2`-basis `β` (any). `N_ν` is the number of qubits (columns of `H_X`); the
conclusion includes `N_ν → ∞`, which the proof establishes (p.33) and Theorem 4.14 uses. The
family is indexed by `ν ∈ ℕ`. -/
theorem theorem_4_12 (t : ℕ) (ht : 4 ≤ t) (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 1 ≤ τ) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 < 1 ∧
    ∀ (k s : ℕ) (n : Fin t → ℕ) (m : Fin t → Bool → ℕ), 2 ≤ k → k + 2 ≤ t → 1 ≤ s →
    (∀ i, 2 ≤ n i) → Monotone n → (∀ i b, 0 < m i b ∧ m i b < n i) →
    (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ →
    ∃ (δ σ : ℝ) (w : ℕ), 0 < δ ∧ 0 < σ ∧ 1 ≤ w ∧
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam0 →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ s →
    ∀ (X : ℕ → Type) [∀ ν, PartialOrder (X ν)] [∀ ν, Fintype (X ν)]
      (φ : ∀ ν, X ν → Fin t → Option Bool) (Fs : ∀ ν, Cosheaf (X ν) F)
      (D : ∀ ν, BaseCodeData (φ ν) (Fs ν) m),
    FamilyHyp.{u} t n m ρ lam X φ Fs D →
    ∀ β : F ≃+ (Fin s → ZMod 2),
    Filter.Tendsto (fun ν => Fintype.card ((Σ f : Face (φ ν) k, Fin ((Fs ν).d f.1)) × Fin s))
      Filter.atTop Filter.atTop ∧
    ∀ ν : ℕ,
      (∀ J' : Finset (Fin t), J'.card = k →
        rateGamma n m k J' / esym (rateS n m) (t - k) ≤
          (logicalQubits (cssHX (φ ν) (Fs ν) β k) (cssHZ (φ ν) (Fs ν) β k) : ℝ) /
            (Fintype.card ((Σ f : Face (φ ν) k, Fin ((Fs ν).d f.1)) × Fin s) : ℝ)) ∧
      ENNReal.ofReal
          (δ * (Fintype.card ((Σ f : Face (φ ν) k, Fin ((Fs ν).d f.1)) × Fin s) : ℝ)) ≤
        ((cssDist (cssHX (φ ν) (Fs ν) β k) (cssHZ (φ ν) (Fs ν) β k) : ℕ∞) : ENNReal) ∧
      IsLocallyTestable w σ (cssHX (φ ν) (Fs ν) β k) (cssHZ (φ ν) (Fs ν) β k) ∧
      ∀ q, qubitDegree (cssHX (φ ν) (Fs ν) β k) (cssHZ (φ ν) (Fs ν) β k) q ≤ w := by sorry

end GoodQLTC
