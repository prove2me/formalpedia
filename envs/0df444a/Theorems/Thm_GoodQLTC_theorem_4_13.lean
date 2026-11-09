-- Prove2me | Theorems.Thm_GoodQLTC_theorem_4_13
-- name    : GoodQLTC.theorem_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:58:42.945003+00:00
-- url     : https://prove2.me/theorems/a06d61c4-f1a4-4a5c-b315-2643db71a540
-- title:
--   Theorem 4.13: realization by arithmetic complexes
-- statement:
--   For every pair of integers $t\ge4$ and $2\le k\le t-2$ there are fixed parameters $s,\{n_i\},\{m_{i,b}\},\rho,\tau,\lambda$ and a family $\{(X_\nu,\mathcal F_\nu)\}$ satisfying the hypotheses of Theorem 4.12, with $\Gamma_k(J)>0$ for some $J\subseteq[t]$ of size $k$; the associated CSS check matrices can be constructed in time polynomial in their blocklength.
--
--   Precisely: there are $\tau\ge1$ and $\rho\in(0,1]$ such that for every $\lambda_0>0$ (in particular $\lambda_0(t,\rho,\tau)$ of Theorem 4.12) there are $s\ge1$, degrees $2\le n_1\le\dots\le n_t$ with $n_t/n_1\le\tau$, dimensions $0<m_{i,b}<n_i$, $0\le\lambda\le\lambda_0$, $J$ with $|J|=k$ and $\Gamma_k(J)>0$, a field with $2^s$ elements, a family satisfying (1)–(3), a basis $\beta$, and orderings of qubits and checks for which one Turing machine computes $\nu\mapsto(H_X^\nu,H_Z^\nu)$ in time polynomial in $N_\nu$.
--
--   Differences from the source:
--   - generalization: λ ≤ λ_0 with λ_0 = λ_0(t, ρ, τ) of Theorem 4.12 → λ ≤ λ_0 for every λ_0 > 0 given after τ and ρ; reason: the proof (p.58) fixes ρ, τ, then λ_0, then the remaining parameters; the source's λ_0 is one such threshold
--   - encoding: constructed in time polynomial in the blocklength → one TM2 machine, input ν in unary, running time ≤ p(N_ν) for one polynomial p, output the injective encoding of the reindexed matrices; reason: Lemma 14.2 (input ν, time polynomial in N_ν); orderings of qubits and checks are part of the output
--   - encoding: universal product expansion over every extension → over every extension in a universe u, for each u; reason: product expansion over E is decided by finitely generated subextensions, so all universes give the same property
--   - encoding: families indexed by ν ≥ 1 → families indexed by ν ∈ ℕ; reason: index shift; same instances
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 4.13, p.19 (PDF p.22); proof p.58; Lemma 14.2, p.56

import Mathlib
import Definitions.Def_GoodQLTC_cssHX
import Definitions.Def_GoodQLTC_rateGamma
import Definitions.Def_GoodQLTC_FamilyHyp
import Definitions.Def_GoodQLTC_IsPolyTimeInBlocklength

namespace GoodQLTC

universe u

/-- **Theorem 4.13** (realization), Gay–Jeronimo, arXiv:2609.20780 (held version), p.19: for every
pair of integers `t ≥ 4` and `2 ≤ k ≤ t − 2`, there are fixed parameters `s, {n_i}, {m_{i,b}}, ρ,
τ` and `λ`, and a family `{(X_ν, F_ν)}` satisfying the hypotheses of Theorem 4.12, with
`Γ_k(J) > 0` for some `J ⊆ [t]` of size `k`. The associated CSS check matrices can be
constructed in time polynomial in their blocklength.

**Formalization Note.** Order of constants as in §2.6 (p.13) and the proof (p.58): `τ` and `ρ` are
fixed first; then, for every threshold `λ_0 > 0` (in particular `λ_0(t, ρ, τ)` of Theorem 4.12),
there are `s, n, m, λ ≤ λ_0`, `J`, a field `F` with `2^s` elements, a family satisfying (1)–(3)
(`FamilyHyp`) with the numerical side conditions of Theorem 4.12, an `F_2`-basis `β`, and orderings
of the qubits and checks, such that one Turing machine computes `ν ↦ (H_X^ν, H_Z^ν)` of (4.5) in
time polynomial in `N_ν` (`IsPolyTimeInBlocklength`). -/
theorem theorem_4_13 (t k : ℕ) (ht : 4 ≤ t) (hk : 2 ≤ k) (hkt : k + 2 ≤ t) :
    ∃ τ ρ : ℝ, 1 ≤ τ ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ lam0 : ℝ, 0 < lam0 →
    ∃ (s : ℕ) (n : Fin t → ℕ) (m : Fin t → Bool → ℕ) (lam : ℝ) (J : Finset (Fin t)),
      1 ≤ s ∧ (∀ i, 2 ≤ n i) ∧ Monotone n ∧ (∀ i b, 0 < m i b ∧ m i b < n i) ∧
      (n ⟨t - 1, by omega⟩ : ℝ) / (n ⟨0, by omega⟩ : ℝ) ≤ τ ∧ 0 ≤ lam ∧ lam ≤ lam0 ∧
      J.card = k ∧ 0 < rateGamma n m k J ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ s ∧
      ∃ (X : ℕ → Type) (_ : ∀ ν, PartialOrder (X ν)) (_ : ∀ ν, Fintype (X ν))
        (φ : ∀ ν, X ν → Fin t → Option Bool) (Fs : ∀ ν, Cosheaf (X ν) F)
        (D : ∀ ν, BaseCodeData (φ ν) (Fs ν) m),
      FamilyHyp.{u} t n m ρ lam X φ Fs D ∧
      ∃ (β : F ≃+ (Fin s → ZMod 2)) (N mX mZ : ℕ → ℕ)
        (eN : ∀ ν, Fin (N ν) ≃ (Σ f : Face (φ ν) k, Fin ((Fs ν).d f.1)) × Fin s)
        (eX : ∀ ν, Fin (mX ν) ≃ (Σ g : Face (φ ν) (k + 1), Fin ((Fs ν).d g.1)) × Fin s)
        (eZ : ∀ ν, Fin (mZ ν) ≃ (Σ g : Face (φ ν) (k - 1), Fin ((Fs ν).d g.1)) × Fin s),
      IsPolyTimeInBlocklength N fun ν =>
        cssData ((cssHX (φ ν) (Fs ν) β k).submatrix (eX ν) (eN ν))
          ((cssHZ (φ ν) (Fs ν) β k).submatrix (eZ ν) (eN ν)) := by sorry

end GoodQLTC
