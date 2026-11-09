-- Prove2me | Theorems.Thm_IntADSat_theorem_B_1
-- name    : IntADSat.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:28.392195+00:00
-- url     : https://prove2.me/theorems/50ad5810-1479-4577-9569-172132d53d75
-- title:
--   Theorem B.1 — integer generation with controlled denominators
-- statement:
--   Let $G\sim G(n,1/2)$, let $\Delta_G=\prod_{d<h\in\mathcal D_G}(h-d)$ be the product of the differences of distinct degrees, $w_G=\max_v\deg_G(v)-\min_v\deg_G(v)$, and $\Lambda^{[2]}_G$ the integer span of $D^ie, D^iAD^je, D^iAD^jAD^\ell e$ ($0\le i,j,\ell\le q-1$). Then
--
--   $$
--   \Pr\big[\Delta_G^3\mathbb Z^n\not\subseteq\Lambda^{[2]}_G\big]\le n^{-3/20+o(1)} .
--   $$
--
--   In particular, $\Delta_G^3\mathbb Z^n\subseteq\Lambda_G$ with probability $1-o(1)$. On this event, $\mathbb Z^n/\Lambda_G$ is finite and its exponent divides $\Delta_G^3$. Consequently, on one event of probability $1-o(1)$,
--
--   $$
--   \mathbb F_p\langle A \bmod p, D\bmod p\rangle(e\bmod p)=\mathbb F_p^n\qquad\text{for every prime } p\nmid\Delta_G ,
--   $$
--
--   and in particular simultaneously for every prime $p>w_G$.
--
--   The theorem confines the possible prime divisors of the integer defect to the divisors of $\Delta_G$, all at most $n-1$.
--
--   Differences from the source:
--   - reading: probability at most n^(−3/20+o(1)) → for every δ > 0, eventually probability ≤ n^(−3/20+δ); reason: equivalent to the existence of ε(n) → 0 with bound n^(−3/20+ε(n)); the standard meaning of o(1) in an exponent of an upper bound
--   - reading: "In particular … with probability 1 − o(1)" and "Consequently, on one event of probability 1 − o(1) … for every prime p ∤ Δ_G. In particular … every prime p > w_G" → one Tendsto to 1 of the conjunction: Δ_G³ℤⁿ ⊆ Λ_G, M_p full for all primes p ∤ Δ_G, M_p full for all primes p > w_G; reason: the page asks for a single event carrying all three
--   - encoding: p > w_G = max deg − min deg → deg u − deg v < p for all vertices u, v; reason: same condition, defined for every n
--   - generalization: on this event ℤⁿ/Λ_G is finite and its exponent divides Δ_G³ → for every n and every graph with Δ_G³ℤⁿ ⊆ Λ_G; reason: deterministic implication; specializes to the event
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorem B.1, p.14 (PDF 15)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_lattice2
import Definitions.Def_IntADSat_Delta
import Definitions.Def_IntADSat_deg

set_option autoImplicit false

namespace IntADSat

/-- **Theorem B.1 (Integer generation with controlled denominators)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.14 (PDF 15)). If
`G ∼ G(n, 1/2)`, then `Pr[Δ_G³ℤⁿ ⊄ Λ_G^{[2]}] ≤ n^{−3/20+o(1)}`. In particular, `Δ_G³ℤⁿ ⊆ Λ_G`
with probability `1 − o(1)`. On this event, `ℤⁿ/Λ_G` is finite and its exponent divides `Δ_G³`.
Consequently, on one event of probability `1 − o(1)`, `𝔽_p⟨A mod p, D mod p⟩(e mod p) = 𝔽_pⁿ` for
every prime `p ∤ Δ_G`. In particular, this holds simultaneously for every prime `p > w_G`.

**Formalization Note** `n^{−3/20+o(1)}` is read as: for every `δ > 0`, eventually at most
`n^{−3/20+δ}`. The "In particular" and "Consequently" clauses are one event of probability tending to
`1` (the conjunction); `p > w_G = max deg − min deg` is written `deg u − deg v < p` for all `u, v`. -/
theorem theorem_B_1 :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in Filter.atTop,
      LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G => ¬ ∀ x : Fin n → ℤ, ((Delta G : ℤ) ^ 3) • x ∈ lattice2 G) ≤
        (n : ℝ) ^ (-(3 / 20 : ℝ) + δ)) ∧
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G =>
        (∀ x : Fin n → ℤ, ((Delta G : ℤ) ^ 3) • x ∈ wordLattice G) ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ Delta G → wordModule (ZMod p) G = ⊤) ∧
        (∀ p : ℕ, p.Prime → (∀ u v : Fin n, (deg G u : ℤ) - deg G v < p) → wordModule (ZMod p) G = ⊤)))
      Filter.atTop (nhds 1) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ x : Fin n → ℤ, ((Delta G : ℤ) ^ 3) • x ∈ wordLattice G) →
      Finite ((Fin n → ℤ) ⧸ wordLattice G) ∧
        AddMonoid.exponent ((Fin n → ℤ) ⧸ wordLattice G) ∣ Delta G ^ 3) := by sorry

end IntADSat
