-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_15
-- name    : OptLocalHamSim.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:10.615881+00:00
-- url     : https://prove2.me/theorems/5f69e7bd-e2b3-4863-804f-8b8e6ab7c7b5
-- title:
--   Lemma 15 — full-output bound for one-step oblivious amplitude amplification: $\|\mathcal U\iota_0-\iota_0U\|\le3\delta+\delta^2\le4\delta$
-- statement:
--   Let $W,S,D$ be finite registers with zero states and $B$ a unitary on $W\otimes S\otimes D$ that maps the zero-work subspace $\mathcal K=\mathrm{ran}\,\iota_{\mathrm{sig}}$ into itself and satisfies $\iota_0^\dagger B\iota_0=\hat A/2$ for a matrix $\hat A$ on $D$. With $R_{\mathrm{sig}}:=I_W\otimes(2|0\rangle\langle0|_S-I_S)\otimes I_D$ and $\mathcal U:=-BR_{\mathrm{sig}}B^\dagger R_{\mathrm{sig}}B$,
--
--   $$
--   \mathcal U\iota_0=\iota_0\hat A+B\iota_0\bigl(I-\hat A^\dagger\hat A\bigr),
--   $$
--
--   and for every unitary $U$ on $D$ with $\delta:=\|\hat A-U\|\le1$,
--
--   $$
--   \|\mathcal U\iota_0-\iota_0U\|\le3\delta+\delta^2\le4\delta .
--   $$
--
--   The bound covers the entire output, including the ancillas, which is what lets block circuits be composed in Theorem 16.
--
--   Differences from the source:
--   - generalization: the block circuit B of eq. (15) and the LCU operator Â_Q → arbitrary finite registers W, S, D, any unitary B preserving K, any matrix Â; reason: the proof uses only these hypotheses; the source's B and Â_Q satisfy them (p.33)
--   - encoding: B preserving K → B maps ι_sig v into the range of ι_sig for every v; reason: the same property
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 15, eqs. (86)–(89), pp.32–33

import Mathlib
import Definitions.Def_OptLocalHamSim_oaaCircuit

open scoped Matrix Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Lemma 15 (Full-output bound for one-step oblivious amplitude amplification)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.33. Let B be
a unitary preserving K and satisfying ι₀†Bι₀ = Â_Q/2. The signal reflection and amplified circuit are
R_sig := I_W ⊗ (2|0⟩⟨0|_S − I_S) ⊗ I_D, 𝒰 := −BR_sigB†R_sigB (87). The full output satisfies
𝒰ι₀ = ι₀Â_Q + Bι₀(I − Â_Q†Â_Q) (88). For every data unitary U with δ := ‖Â_Q − U‖ ≤ 1, the error obeys
‖𝒰ι₀ − ι₀U‖ ≤ 3δ + δ² ≤ 4δ (89).

**Formalization Note** Stated for arbitrary finite work, signal and data registers `W`, `S`, `Dd` with
zero states `w0`, `s0`, the full space ordered `W ⊗ S ⊗ D`, any matrix `Â` on the data, and any
unitary `B` mapping `K = ran ι_sig` into itself (`PreservesK`); `ι_sig`, `ι₀` as in (86). -/
theorem lemma_15 {W S Dd : Type} [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S]
    [Fintype Dd] [DecidableEq Dd] (w0 : W) (s0 : S)
    (B : Matrix (W × (S × Dd)) (W × (S × Dd)) ℂ) (hB : B ∈ Matrix.unitaryGroup (W × (S × Dd)) ℂ)
    (hK : PreservesK (S := S) (Dd := Dd) w0 B) (Ahat : Matrix Dd Dd ℂ)
    (hA : (iotaZero (Dd := Dd) w0 s0)ᴴ * B * iotaZero (Dd := Dd) w0 s0 = (1 / 2 : ℂ) • Ahat) :
    oaaCircuit s0 B * iotaZero (Dd := Dd) w0 s0 =
        iotaZero (Dd := Dd) w0 s0 * Ahat + B * iotaZero (Dd := Dd) w0 s0 * (1 - Ahatᴴ * Ahat) ∧
      ∀ U : Matrix Dd Dd ℂ, U ∈ Matrix.unitaryGroup Dd ℂ → ‖Ahat - U‖ ≤ 1 →
        ‖(oaaCircuit s0 B * iotaZero (Dd := Dd) w0 s0 - iotaZero (Dd := Dd) w0 s0 * U :
            Matrix (W × (S × Dd)) Dd ℂ)‖ ≤
            3 * ‖Ahat - U‖ + ‖Ahat - U‖ ^ 2 ∧
          3 * ‖Ahat - U‖ + ‖Ahat - U‖ ^ 2 ≤ 4 * ‖Ahat - U‖ := by sorry

end OptLocalHamSim
