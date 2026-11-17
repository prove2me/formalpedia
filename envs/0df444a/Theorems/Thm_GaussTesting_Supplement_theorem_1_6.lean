-- Prove2me | Theorems.Thm_GaussTesting_Supplement_theorem_1_6
-- name    : GaussTesting.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:27:36.128036+00:00
-- url     : https://prove2.me/theorems/b713fd98-fb1e-4c56-8aec-58cacc5e5d59
-- title:
--   Theorem 1.6 — testing lower bounds: every $t$-copy tester needs $t=\Omega(\log(1/\delta)/(\varepsilon_2-\varepsilon_1)^2)$ (corrected: $n\ge1$ modes)
-- statement:
--   Let $\mathcal C$ be one of the five classes of Theorem 1.4 on $n$ modes: pure fermionic Gaussian states $G_f$ or Slater determinants $\mathcal S$ in the fermionic Fock space $\bigwedge\mathbb C^n$, or pure bosonic Gaussian states $G_b$, zero-mean bosonic Gaussian states $G_{b,0}$ or coherent states $\mathrm{Coh}_n$ in the bosonic Fock space $\bigvee\mathbb C^n$. For each class there is a constant $c>0$ such that for every number of modes $n\ge1$, all
--
--   $$
--   0\le\varepsilon_1<\varepsilon_2\le\frac1{\sqrt2},\qquad 0<\delta<\frac14,
--   $$
--
--   and every $t$-copy $(\varepsilon_1,\varepsilon_2,\delta)$-tester for $\mathcal C$ (Definition 1.2: any two-outcome measurement on $|\psi\rangle^{\otimes t}$ that accepts with probability at least $1-\delta$ when $\mathrm{dist}(\psi,\mathcal C)\le\varepsilon_1$ and at most $\delta$ when $\mathrm{dist}(\psi,\mathcal C)\ge\varepsilon_2$, for every pure state $\psi$ of the whole Fock space),
--
--   $$
--   t\ \ge\ c\,\frac{\log(1/\delta)}{(\varepsilon_2-\varepsilon_1)^2}.
--   $$
--
--   For intolerant testing ($\varepsilon_1=0$, $\varepsilon_2=\varepsilon$) this matches the $O(\log(1/\delta)/\varepsilon^2)$ upper bound of Theorem 1.4, so the testers of the mission are optimal; for tolerant testing it is tight up to the constant $\beta$ of Theorem 1.4.
--
--   **Formalization Note** The statement is a conjunction of five clauses, one per class, each with its own $c$ chosen before $n$, $\varepsilon_1$, $\varepsilon_2$, $\delta$ and the tester. Testers are `IsCopyTester`, i.e. arbitrary effects on $t$ copies, not only block testers. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: every number of modes n (the n-mode classes of Theorem 1.4) → n ≥ 1; reason: at n = 0 every Fock space is one-dimensional, every unit vector is in the class up to phase, so the far case never occurs and M = I on t = 0 copies is a (ε₁, ε₂, δ)-tester, contradicting t ≥ c·log(1/δ)/(ε₂−ε₁)² > 0
--   - reading: t = Ω(log(1/δ)/(ε₂ − ε₁)²) → for each class one constant c > 0, chosen before n, ε₁, ε₂, δ and the tester, with c·log(1/δ)/(ε₂ − ε₁)² ≤ t; reason: the Ω is uniform in all parameters (the proof gives c = 1/20 for all five classes); natural log
--   - encoding: any quantum algorithm on |ψ⟩^{⊗t} with output ACCEPT/REJECT (Definition 1.2; A : Sym^t(ℋ) → {ACCEPT, REJECT}) → any effect M on ℋ^{⊗t} (M ≥ 0, I − M ≥ 0), accepting with probability Re⟨ψ^{⊗t}, M ψ^{⊗t}⟩; reason: by Naimark dilation every binary-output algorithm, with ancillas and adaptivity, is such an effect and every effect is realized; effects on Sym^t(ℋ) and on ℋ^{⊗t} give the same acceptance probabilities on ψ^{⊗t}
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ; ℋ^{⊗t} → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗t} is ℓ²(Fin t → ι); reason: unitarily the same spaces; the base mission's convention
--   - encoding: classes of pure states (rays) → the published sets Gf, Slater, Gb, Gb0, Coh of unit vectors, closed under global phase; reason: dist(ψ, 𝒞) is phase-invariant
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 1.6, p.6; Definition 1.2, p.4; §9, pp.75–82 (proof)

import Definitions.Def_GaussTesting_Supplement_IsCopyTester
import Definitions.Def_GaussTesting_Slater
import Definitions.Def_GaussTesting_Gb
import Definitions.Def_GaussTesting_Gb0
import Definitions.Def_GaussTesting_Coh

namespace GaussTesting

namespace Supplement

/-- **Theorem 1.6 (Testing lower bounds).** Let `𝒞` be one of the classes of Theorem 1.4 (fermionic
Gaussian states `G_f`, Slater determinants `𝒮`, bosonic Gaussian states `G_b`, zero-mean bosonic Gaussian
states `G_{b,0}`, coherent states `Coh_n`), and `0 ≤ ε₁ < ε₂ ≤ 1/√2`, `0 < δ < 1/4`. If there is a
`t`-copy `(ε₁, ε₂, δ)`-tester for `𝒞`, then `t = Ω(log(1/δ)/(ε₂ − ε₁)²)`: for each class there is a
constant `c > 0` such that for every number of modes `n ≥ 1`, all such `ε₁, ε₂, δ` and every `t`-copy
tester, `t ≥ c · log(1/δ)/(ε₂ − ε₁)²`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 1.6, p.6; Definition 1.2, p.4; proved in §9,
pp.75–82.

**Formalization Note.**
* "`t`-copy tester" is `IsCopyTester`: any effect on `ℋ^{⊗t}`, i.e. any quantum algorithm with binary
  output on `|ψ⟩^{⊗t}`, not only block testers.
* The `Ω` constant `c` is chosen per class before `n, ε₁, ε₂, δ, t`; `log` is natural.
* `n ≥ 1`: at `n = 0` the Fock space is one-dimensional, every unit vector lies in the class (up to
  phase), and the effect `1` on `t = 0` copies is a tester, so the printed bound fails there.
* The classes are the published `Gf`, `Slater`, `Gb`, `Gb0`, `Coh` of the base mission (all parities,
  all particle numbers, no energy bound), each on the whole Fock space. -/
theorem theorem_1_6 :
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 / Real.sqrt 2 →
      0 < δ → δ < 1 / 4 →
      ∀ (t : ℕ) (M : Ell2 (Fin t → FermiCap.Gaussian.Qubits n) →L[ℂ]
          Ell2 (Fin t → FermiCap.Gaussian.Qubits n)),
        IsCopyTester (Gf n) t M ε₁ ε₂ δ → c * Real.log (1 / δ) / (ε₂ - ε₁) ^ 2 ≤ t) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 / Real.sqrt 2 →
      0 < δ → δ < 1 / 4 →
      ∀ (t : ℕ) (M : Ell2 (Fin t → FermiCap.Gaussian.Qubits n) →L[ℂ]
          Ell2 (Fin t → FermiCap.Gaussian.Qubits n)),
        IsCopyTester (Slater n) t M ε₁ ε₂ δ → c * Real.log (1 / δ) / (ε₂ - ε₁) ^ 2 ≤ t) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 / Real.sqrt 2 →
      0 < δ → δ < 1 / 4 →
      ∀ (t : ℕ) (M : Ell2 (Fin t → Fin n → ℕ) →L[ℂ] Ell2 (Fin t → Fin n → ℕ)),
        IsCopyTester (Gb n) t M ε₁ ε₂ δ → c * Real.log (1 / δ) / (ε₂ - ε₁) ^ 2 ≤ t) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 / Real.sqrt 2 →
      0 < δ → δ < 1 / 4 →
      ∀ (t : ℕ) (M : Ell2 (Fin t → Fin n → ℕ) →L[ℂ] Ell2 (Fin t → Fin n → ℕ)),
        IsCopyTester (Gb0 n) t M ε₁ ε₂ δ → c * Real.log (1 / δ) / (ε₂ - ε₁) ^ 2 ≤ t) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε₁ ε₂ δ : ℝ, 0 ≤ ε₁ → ε₁ < ε₂ → ε₂ ≤ 1 / Real.sqrt 2 →
      0 < δ → δ < 1 / 4 →
      ∀ (t : ℕ) (M : Ell2 (Fin t → Fin n → ℕ) →L[ℂ] Ell2 (Fin t → Fin n → ℕ)),
        IsCopyTester (Coh n) t M ε₁ ε₂ δ → c * Real.log (1 / δ) / (ε₂ - ε₁) ^ 2 ≤ t) := by sorry

end Supplement

end GaussTesting
