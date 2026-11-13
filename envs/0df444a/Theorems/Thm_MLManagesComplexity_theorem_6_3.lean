-- Prove2me | Theorems.Thm_MLManagesComplexity_theorem_6_3
-- name    : MLManagesComplexity.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:03.319594+00:00
-- url     : https://prove2.me/theorems/b09dc925-29ce-4930-8ab4-79d496b63585
-- title:
--   Theorem 6.3 — an efficient model that fits a PRG's output as well as uniform has negligible $\mathrm{KL}(U\|\mu)$
-- statement:
--   Let $G=(G_n)$ be a cryptographic pseudorandom generator with seed length $\ell$, let $D_n$ be its output distribution on $\{0,1\}^n$ (the image of a uniform seed), and let $U_n$ be the uniform distribution on $\{0,1\}^n$. Suppose $\mu=(\mu_n)$ is a P/poly-computable family of distributions with polynomially-bounded max-entropy such that
--
--   $$
--   \mathrm{KL}(D_n\|\mu_n)\ \le\ \mathrm{KL}(D_n\|U_n)\qquad\text{for every } n .
--   $$
--
--   Then $\mathrm{KL}(U_n\|\mu_n)$ is negligible in $n$: there is a negligible real-valued function $\nu$ with
--
--   $$
--   \mathrm{KL}(U_n\|\mu_n)\ \le\ \nu(n)\qquad\text{for every } n .
--   $$
--
--   This is the paper's main theorem. Although the generator's output and the uniform distribution are only computationally indistinguishable, any efficiently computable model with bounded max-entropy that models the generator's output at least as well as the uniform distribution does is information-theoretically close to uniform: the model treats pseudorandomness as randomness.
--
--   **Formalization Note** KL is in bits, valued in the extended reals ($+\infty$ on a support mismatch); since $\nu$ is real valued the conclusion includes that $\mathrm{KL}(U_n\|\mu_n)$ is finite.
--
--   Differences from the source:
--   - encoding: distributions and quantities on {0,1}^n, with "negligible in n" and polynomial bounds understood asymptotically → families indexed by n (`DistFamily := (n : ℕ) → PMF (Fin n → Bool)`), strings as `Fin n → Bool`, bit x_i = `x ⟨i−1,_⟩`; reason: asymptotic statements are about families; the same instances
--   - encoding: circuits with at most n^c gates (P/poly) → well-formed circuits of size (inputs + gates) at most (n+2)^c; reason: both describe all polynomial bounds; n^c is 0 or 1 at n ≤ 1
--   - generalization: polynomially-bounded max-entropy: µ(x) ≥ 2^{−n^k} for some k → µ_n(x) ≥ 2^{−(n+2)^k} for some k; reason: the source's bound implies this one, so every µ the source allows is allowed; the literal bound at n = 1 would force µ_1 uniform
--   - reading: "P/poly algorithm" distinguishers (Theorem 6.1; §3.3 says "probabilistic P/poly algorithms") → polynomial-size families of probabilistic Boolean circuits, coin inputs counted in the size; reason: §3.3 and the proof of Theorem 6.1 (A outputs 1 with probability g(x)/n^c) use probabilistic algorithms; for nonuniform families fixing the best coins gives a deterministic family of no larger size, so the two readings define the same notion
--   - reading: G is computable in polynomial time → one polynomial-time machine maps 1^n 0 followed by the seed s to G_n(s); reason: the source does not say polynomial in which length; G is a family indexed by the output length n, and the unary n lets the machine run in time polynomial in n even when ℓ(n) ≪ n; this is the more permissive reading (every G computable in time polynomial in its seed length with n polynomial in ℓ qualifies), so the goal covers every generator of the source, and the proof uses only the security clause
--   - encoding: outputs of length n > ℓ → ℓ(n) < n for every n ≥ 1; reason: at n = 0 no seed length is below 0; requiring it there would make the definition unsatisfiable
--   - encoding: "≤ negl(n)" / "is negligible in n" → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n, (quantity at n) ≤ ν n; reason: the source's abuse of notation (§3, p.4); for the nonnegative KL it says exactly that KL is bounded by a negligible function
--   - encoding: KL-divergence and cross-entropy (possibly infinite, p.5: "even infinite if for some x, τ(x) > µ(x) = 0") → the published `klBits`/`crossEntropy` in `EReal`, `⊤` exactly on a support mismatch, logarithms base 2; reason: Lean convention; same values
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem 6.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_MLManagesComplexity_PPolyComputable
import Definitions.Def_MLManagesComplexity_PolyMaxEntropy
import Definitions.Def_MLManagesComplexity_IsCryptoPRG

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity

/-- **Theorem 6.3** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), printed p.11, PDF p.12). Let `G` be a cryptographic pseudorandom
generator with seed length `ℓ`, `Dₙ` its output distribution on `{0,1}^n`, and `Uₙ` the uniform
distribution. If `μ` is a P/poly-computable family with polynomially-bounded max-entropy such that
`KL(Dₙ‖μₙ) ≤ KL(Dₙ‖Uₙ)` for every `n`, then `KL(Uₙ‖μₙ)` is negligible: there is a negligible
real `ν` with `KL(Uₙ‖μₙ) ≤ ν(n)` for every `n`.

**Formalization Note** KL in bits, in `EReal` (published `klBits`); `ν` is real valued, so the
conclusion includes finiteness of `KL(Uₙ‖μₙ)`. Since KL is nonnegative, this is "KL(U‖μ) is
negligible in n". -/
theorem theorem_6_3 (ℓ : ℕ → ℕ) (G : (n : ℕ) → (Fin (ℓ n) → Bool) → (Fin n → Bool))
    (hG : IsCryptoPRG ℓ G) (μ : DistFamily) (hμ : PPolyComputable μ) (hmax : PolyMaxEntropy μ)
    (hfit : ∀ n : ℕ, klBits (prgDist ℓ G n) (μ n) ≤ klBits (prgDist ℓ G n) (uniformFamily n)) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n : ℕ, klBits (uniformFamily n) (μ n) ≤ ((ν n : ℝ) : EReal) := by sorry

end MLManagesComplexity
