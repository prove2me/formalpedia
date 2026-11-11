-- Prove2me | Theorems.Thm_LindbladShallow_theorem_2_1
-- name    : LindbladShallow.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:22:53.073797+00:00
-- url     : https://prove2.me/theorems/466f3b6b-3e0e-4772-b791-6b67c467d0ec
-- title:
--   Theorem 2.1 — simulation of geometrically local Lindblad dynamics
-- statement:
--   Fix the local parameters $D,d_0,\kappa,r_*,\mu_*,d_{\mathrm{inc}}$. There are a constant $C_D>0$, a deterministic Turing machine and a polynomial such that for every valid input — a generator $\mathcal L$ of the form of Eq. (1) on $n$ sites of $\mathbb Z^D$ with $\mathbb Q+i\mathbb Q$ local terms satisfying the local assumptions, a rational time $T>0$ and a rational tolerance $0<\epsilon<1$ — the machine outputs, in time polynomial in the input length plus $G+N_{\mathrm{fresh}}$ (hence polynomial in the input and output-description lengths), the description of a well-formed segmented circuit over the gate set
--   $$\mathcal G=\{H,X,Z,S,S^\dagger,T,T^\dagger,CX,A_x,A_x^\dagger,A_z,A_z^\dagger\},$$
--   nearest-neighbour on a refinement of the lattice, whose channel $\widetilde\Phi_T$ satisfies
--   $$\big\|\widetilde\Phi_T-e^{T\mathcal L}\big\|_\diamond\le\epsilon$$
--   and
--   $$G\le C_Dn(1+\lambda T)(1+\log X)^{16D+4},\qquad d_{NN}\le C_D(1+\lambda T)(1+\log X)^{16D+4},$$
--   $$Q_{\mathrm{peak}}\le C_Dn(1+\log X)^{6D},\qquad N_{\mathrm{fresh}}\le C_Dn(1+\lambda T)(1+\log X)^{6D},$$
--   with $\lambda$ and $X=\max\{2,n(1+\lambda T)/\epsilon\}$ as in Eq. (2) and $\log$ natural.
--
--   This is the paper's full resource statement: nearly linear gate count $O(nT\,\mathrm{polylog})$ and depth $O(T\,\mathrm{polylog})$ for static finite-range Lindblad dynamics with noncommuting jumps, over a fixed finite gate set (Theorem A is its case $\lambda=O(1)$, $T\ge1$).
--
--   Differences from the source:
--   - reading: a deterministic classical algorithm … in time polynomial in the input and output-description lengths → one Mathlib Turing.FinTM2 machine (alphabets ≃ Sym) that halts on encInst I with output encCirc c within p(|encInst I| + G + N_fresh) steps, chosen before the input; since G + N_fresh ≤ |encCirc c| this implies the bound p(|encInst I| + |encCirc c|); reason: the paper fixes no machine model; length-faithful encodings make the clause non-vacuous, and measuring the output by G + N_fresh blocks padding (empty segments or a far idle auxiliary inflate |encCirc c| at no resource cost and would admit an exponential-time machine); the paper's description (gates and wire indices, p.10) has length polynomial in the input, G and N_fresh
--   - reading: every logical qubit has a fixed position on a lattice refinement → system qubit (x, k) at f·x + u_k with u injective into {0, …, f−1}^D; auxiliary qubits at distinct other points of ℤ^D; reason: the layout of §5.5, p.47
--   - reading: nearest-neighbour gates → every CX acts on two positions at ℓ¹ distance exactly 1; reason: grid adjacency, used by the routing of Lemma 5.8; the stronger reading
--   - reading: segments and the counts G, d_NN, Q_peak, N_fresh → a list of segments, each with fresh |0⟩ auxiliaries, layers of gates and a final discard; G = all gates, d_NN = all layers, Q_peak = n·d0 + max_s |aux_s|, N_fresh = Σ_s |aux_s|; reason: the definitions of p.10 and Eq. (47)
--   - encoding: ‖Φ̃_T − e^{Tℒ}‖_⋄ ≤ ϵ → dnorm ≤ ofReal ϵ, an ℝ≥0∞ supremum over every r ≥ 1 and nonzero Z, reference factor first; reason: same norm; no junk value
--   - encoding: preprocessing removes empty-support and zero terms → such terms may appear in a valid input, are exempt from the support and incidence bounds and contribute 0; reason: the paper's preprocessing; λ ranges over retained terms
--   - encoding: local matrices on ordered supports → matrices indexed by support-slot/qubit bit strings with ℚ × ℚ entries, lifted by the identity; reason: Lean typing; same operators
--   - encoding: e^{Tℒ} → NormedSpace.exp of the matrix of Tℒ in the standard basis; reason: basis-independent; the superoperator exponential
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 2.1, p.10 (local model §2.1, p.9; Eq. (2); circuit model p.10; Eq. (47), p.50; Eq. (68), p.69)

import Mathlib
import Definitions.Def_LindbladShallow_gen
import Definitions.Def_LindbladShallow_lam
import Definitions.Def_LindbladShallow_Circuit_channel
import Definitions.Def_LindbladShallow_encInst

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

/-- **Theorem 2.1** (Simulation of geometrically local Lindblad dynamics; Shen–Wu–Yuan–Zhang,
arXiv:2610.05362, held version sha256 8f4637ef…, p.10). For fixed local parameters there are a
constant `C_D > 0`, one deterministic Turing machine and one polynomial such that on every valid
input (a generator of the form of Eq. (1), rational `T > 0`, rational `0 < ϵ < 1`, under the local
assumptions of §2.1) the machine outputs, within time polynomial in the input and
output-description lengths, the description of a well-formed circuit over the gate set of
Eq. (68), nearest-neighbour on a refinement of the lattice, whose channel `Φ̃_T` satisfies
`‖Φ̃_T − e^{Tℒ}‖_⋄ ≤ ϵ` and
`G ≤ C_D n(1 + λT)(1 + log X)^{16D+4}`, `d_NN ≤ C_D(1 + λT)(1 + log X)^{16D+4}`,
`Q_peak ≤ C_D n(1 + log X)^{6D}`, `N_fresh ≤ C_D n(1 + λT)(1 + log X)^{6D}`.

**Formalization Note** The machine is Mathlib's `Turing.FinTM2`, with input and output stack
alphabets identified with `Sym`; it reads `encInst I` and halts with `encCirc c` within
`p(|encInst I| + G + N_fresh)` steps. Since every gate and every auxiliary initialization takes at
least one symbol of `encCirc c`, `G + N_fresh ≤ |encCirc c|`, so this implies the paper's bound
`p(|encInst I| + |encCirc c|)`; it is stated this way because `|encCirc c|` alone can be inflated
at no cost in any resource (empty segments, or an idle auxiliary at an astronomically distant
position), which would let an exponential-time machine meet a bound in `|encCirc c|`. The paper's
own output (gates and wire indices, p.10) has length polynomial in the input length, `G` and
`N_fresh`. The encodings are length-faithful (binary numerals, explicit lists). `C`, the machine and `p` are chosen after the fixed parameters and before the input. The
diamond norm is the unhalved `dnorm`, a supremum over all reference dimensions. -/
theorem theorem_2_1 :
    ∀ P : Params, ∃ C : ℝ, 0 < C ∧
      ∃ (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Sym) (eOut : tm.Γ tm.k₁ ≃ Sym)
        (p : Polynomial ℕ),
      ∀ I : Instance P, I.Valid →
        ∃ c : Circuit P, c.WellFormed I ∧
          Nonempty (Turing.TM2OutputsInTime tm ((encInst I).map eIn.symm)
            (some ((encCirc c).map eOut.symm))
            (p.eval ((encInst I).length + c.gateCount + c.freshInits))) ∧
          dnorm (c.channel I - ⇑(target I)) ≤ ENNReal.ofReal (I.ε : ℝ) ∧
          (c.gateCount : ℝ) ≤
            C * I.n * (1 + lam I * I.T) * (1 + Real.log (bigX I)) ^ (16 * P.D + 4) ∧
          (c.depth : ℝ) ≤
            C * (1 + lam I * I.T) * (1 + Real.log (bigX I)) ^ (16 * P.D + 4) ∧
          (c.peakQubits I : ℝ) ≤ C * I.n * (1 + Real.log (bigX I)) ^ (6 * P.D) ∧
          (c.freshInits : ℝ) ≤
            C * I.n * (1 + lam I * I.T) * (1 + Real.log (bigX I)) ^ (6 * P.D) := by sorry

end LindbladShallow
