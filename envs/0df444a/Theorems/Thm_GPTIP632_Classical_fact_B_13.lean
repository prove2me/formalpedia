-- Prove2me | Theorems.Thm_GPTIP632_Classical_fact_B_13
-- name    : GPTIP632.Classical.fact_B_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:11.850802+00:00
-- url     : https://prove2.me/theorems/9bf63395-51b3-441c-b361-285f7339d4a5
-- title:
--   Fact B.13: channels with classical input and output registers decompose as $\Phi(\delta_i\otimes\tau)=\sum_j\delta_j\otimes\Phi_{ij}(\tau)$
-- statement:
--   Let $\mathcal G$ be a theory satisfying the standing assumptions, let $P,P'$ be systems of $\mathcal G$, and let $\Phi$ be a channel (a map positive on all extensions with respect to the systems of $\mathcal G$, preserving the unit) from $\Delta_n\otimes P$ to $\Delta_k\otimes P'$. There are maps $\Phi_{ij}:V_P\to V_{P'}$ ($1\le i\le n$, $1\le j\le k$), positive on all extensions, with $\sum_ju_{P'}\circ\Phi_{ij}=u_P$ for each $i$, such that
--
--   $$
--   \Phi(\delta_i\otimes\tau)=\sum_j\delta_j\otimes\Phi_{ij}(\tau)\qquad\text{for all }i\text{ and }\tau\in V_P.
--   $$
--
--   If $k=1$, each $\Phi_i:=\Phi_{i1}$ is a channel and $\Phi$ is the classically controlled channel that applies $\Phi_i$ on the input $i$.
--
--   Applied to the prover's channels, this gives the maps $\Pi_i^{qa}$ of eq. (5), on which the reduction of arbitrary provers to classical ones rests.
--
--   Differences from the source:
--   - encoding: a system is (V_A, V_A^+, u_A) with V_A a finite-dimensional real vector space → a system has a finite coordinate type ι with V_A = ι → ℝ, the cone a subset, and the unit a coordinate vector paired by the dot product; reason: every finite-dimensional space is ℝ^ι in a basis; (T4) refers to these fixed coordinates
--   - encoding: the standard classical systems Δ_n (n ≥ 1) → the designated system cl n is Δ_{n+1}, with coordinates Fin (n+1); cl 0 = Δ_1 is the trivial system I; reason: an index shift; Δ_1 has V = ℝ, V⁺ = ℝ≥0, u = id, which is I
--   - generalization: allowed operations are closed under sequential and parallel composition → closure is required for channel∘channel and instrument∘instrument (product outcome set) and for parallel composition of channels and of instruments; compositions mixing a channel with an instrument are not required; reason: fewer requirements on the theory, so more theories qualify; every theory of Definition B.16 satisfies these conditions, so the statement specializes to the source
--   - encoding: If k = 1, Φ is the classically controlled channel that applies Φ_i := Φ_{i1} on the input i → for the output register Δ_1 (k = 0 in the shifted index), each Φ_{i0} is a channel, and Φ(δ_i ⊗ τ) = δ_0 ⊗ Φ_{i0}(τ) by the main formula; reason: Δ_1 ⊗ P' ≅ P'
--   - reading: (T3) every stochastic map between classical systems is an allowed channel → every column-stochastic matrix between systems obtained from the designated Δ_n by forming composites (IsStdClassical), in their own coordinates, is an allowed channel; reason: p.16: for classical A and B the composite is Δ_nm; 'classical' means the effective encodings of (T3), not every simplex (p.23)
--   - encoding: (T3) the readout effects of Δ_n are allowed → the readout measurement of Δ_n, with effects the coordinate functionals, is an allowed instrument to the trivial system; reason: a measurement is an instrument with trivial output (Definition B.11)
--   - reading: (T4) the gate set contains the preparation of a fixed state of each elementary system, the elementary discards, the readout of classical bits, the preparation of a fair coin, and a universal set of classical reversible gates [Tof80] → the classical bit Δ_2 is an elementary system a, and the gate set contains, besides a fixed preparation and the discard of every elementary system, the readout of a, the fair coin on a, the preparation of δ_0 on a, NOT and Toffoli on a; reason: Toffoli universality needs constant bits; with fair coins only, reversible gates never produce a known bit, and the proof of Lemma E.1 (p.24) copies classical registers with reversible gates
--   - encoding: a (deterministic) polynomial-time Turing machine → a deterministic oracle Turing machine (QAdvFew.PoQOracle.OTM) run with the empty oracle for p(|input|) steps, its output read off the work tape; reason: a clocked machine is a polynomial-time machine and conversely
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, p.16 (PDF p.18), Fact B.13

import Mathlib
import Definitions.Def_GPTIP632_Classical_Theory

namespace GPTIP632.Classical

/-- **Fact B.13**, p.16: let `Φ` be a channel (Definition B.11, relative to the systems of the
theory) from `Δ_{n+1} ⊗ P` to `Δ_{k+1} ⊗ P'`. There are maps `Φ_{ij} : V_P → V_{P'}`, positive on
all extensions, with `∑_j u_{P'} ∘ Φ_{ij} = u_P` for each `i`, such that
`Φ(δ_i ⊗ τ) = ∑_j δ_j ⊗ Φ_{ij}(τ)`. If the output register is `Δ_1` (`k = 0`), each `Φ_{i0}` is a
channel and `Φ` applies `Φ_{i0}` on the input `i`. -/
theorem fact_B_13 (G : Theory) (hG : G.Standing) (n k : ℕ) (P P' : G.C.Sys)
    (Φ : Matrix (G.C.sys (G.C.comp (G.C.cl k) P')).ι (G.C.sys (G.C.comp (G.C.cl n) P)).ι ℝ)
    (hΦ : G.C.IsChannel Φ) :
    ∃ Φij : Fin (n + 1) → Fin (k + 1) → Matrix (G.C.sys P').ι (G.C.sys P).ι ℝ,
      (∀ i j, G.C.PosAllExt (Φij i j)) ∧
      (∀ i, ∑ j, Matrix.vecMul (G.C.sys P').unit (Φij i j) = (G.C.sys P).unit) ∧
      (∀ i (τ : (G.C.sys P).ι → ℝ),
        Φ.mulVec (G.C.liftCl n i τ) = ∑ j, G.C.liftCl k j ((Φij i j).mulVec τ)) ∧
      (k = 0 → ∀ i, G.C.IsChannel (Φij i 0)) := by sorry

end GPTIP632.Classical
