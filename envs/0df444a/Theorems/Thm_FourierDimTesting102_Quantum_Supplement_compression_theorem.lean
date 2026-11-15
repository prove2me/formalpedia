-- Prove2me | Theorems.Thm_FourierDimTesting102_Quantum_Supplement_compression_theorem
-- name    : FourierDimTesting102.Quantum.Supplement.compression_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:33:39.438113+00:00
-- url     : https://prove2.me/theorems/52965c47-5692-4fba-a5db-76a83ad69f81
-- title:
--   Theorem 6.1 — random linear compression to $O(k\log\frac1\beta)$ dimensions preserves $\rho_k$ up to $\beta$
-- statement:
--   Let $\mu$ be any probability distribution on $\mathbb F_2^n$ and $0<\beta<1$. There is an absolute constant $C$ such that for every
--
--   $$
--   r\ \ge\ C\,(k+1)\log\frac e\beta ,
--   $$
--
--   a uniformly random linear map $X:\mathbb F_2^n\to\mathbb F_2^r$ satisfies, with probability at least $0.99$,
--
--   $$
--   \rho_k(\mu)-\beta\ \le\ \rho_{k,X}(\mu)\ \le\ \rho_k(\mu),
--   $$
--
--   where $\rho_k(\mu)=\min_{\dim W\le k}\mu(\overline W)$ and $\rho_{k,X}(\mu)=\min_{\dim W\le k}\mu_X(\overline W)$ for the pushforward $\mu_X(t)=\sum_{s:Xs=t}\mu(s)$. For $k\ge1$ and $\beta\le1/2$ the dimension is $O(k\log\frac1\beta)$, independent of $n$.
--
--   The theorem reduces the enumeration of all subspaces of $\mathbb F_2^n$ to subspaces of $\mathbb F_2^r$; with $\mu$ the Fourier distribution of $f$ it is the compression step of the tolerant classical tester (Theorem 6.2), and it holds for arbitrary distributions.
--
--   Differences from the source:
--   - generalization: over X : F₂ⁿ → F₂ʳ where r = O(k log(1/β)) (one r) → every r at least the threshold; reason: the conclusion is claimed for all larger r, which contains the source’s choice
--   - reading: k log(1/β) → (k+1) log(e/β); reason: equal up to a constant factor for k ≥ 1 and β ≤ 1/2; the literal form fails for β near 1: then C k log(1/β) < 1 permits r = 0, where ρ_{k,X} = 0 while ρ_k(µ) − β > 0 for µ uniform on F₂ⁿ with n large
--   - encoding: µ a probability distribution; a uniformly random linear map → µ : V n → ℝ, µ ≥ 0, ∑ µ = 1; X uniform on r × n matrices over ZMod 2; reason: point masses and singular maps included
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, p.27, Theorem 6.1 (proof pp.28–29 with Lemmas 6.1–6.2)

import Definitions.Def_FourierDimTesting102_Quantum_Supplement_Model

namespace FourierDimTesting102.Quantum.Supplement

open QAlgorithms FourierDimTesting102.Quantum

/-- Theorem 6.1, p.27: there is an absolute constant `C` such that for every probability
distribution `μ` on `F₂ⁿ`, every `0 < β < 1` and every `r ≥ C(k+1) log(e/β)`, a uniformly random
linear map `X : F₂ⁿ → F₂ʳ` satisfies `ρ_k(μ) − β ≤ ρ_{k,X}(μ) ≤ ρ_k(μ)` with probability at least
`0.99`. -/
theorem compression_theorem :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k r : ℕ) (μ : V n → ℝ) (β : ℝ), IsProbDist μ → 0 < β → β < 1 →
      C * ((k : ℝ) + 1) * Real.log (Real.exp 1 / β) ≤ r →
      0.99 ≤ unifProb (fun X : LinMap n r =>
        rhoK k μ - β ≤ rhoKX k μ X ∧ rhoKX k μ X ≤ rhoK k μ) := by sorry

end FourierDimTesting102.Quantum.Supplement
