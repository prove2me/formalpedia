-- Prove2me | Theorems.Thm_LindbladShallow_Supplement_theorem_5_1
-- name    : LindbladShallow.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:24:52.085655+00:00
-- url     : https://prove2.me/theorems/510bbdc2-3e90-4714-9642-ea546d6bc212
-- title:
--   Theorem 5.1 — coherent simulation of a local factor with error $\eta$, $G\le C_DZ_*^{10}$, $Q\le C_DZ_*^{6}$, NN cost $C_DH_{\mathrm{host}}Z_*^{10}$
-- statement:
--   Fix the local parameters. Consider a valid input with its prescribed execution of Section 3.3: the coarse-graining length $R$ of Eq. (11), $r$ windows, $M$ periods and step $h=\tau/M$ (Eq. (15)). Let $C$ be an assigned owner cube of colour $c$, with local factor
--   $$
--   W_C=V^{(c)}_{C,r}\cdots V^{(c)}_{C,1}\,V^{(c-1)\dagger}_{C,1}\cdots V^{(c-1)\dagger}_{C,r},
--   $$
--   old inverse windows first (Eq. (16)), acting on the system and the physical baths. The **common bounds** are:
--   1. an integer $v$ bounding the support-box volume $(9R)^D$, the number of system qubits of $\Omega_C$ and the number of terms of the complete owner blocks;
--   2. an integer $w_{\mathrm{reg}}$ bounding every bath-label width $w_{b,A}$ and every occurrence-address width $\lceil\log_2 L\rceil$ of a window with $L$ occurrences;
--   3. a real $\Sigma\ge 0$ and an accuracy $0<\eta<1$.
--
--   Put
--   $$
--   Z_*:=2+v+w_{\mathrm{reg}}+\lceil\Sigma\rceil+\lceil\log_2(1/\eta)\rceil.
--   $$
--
--   **Theorem.** There is a constant $C_D>0$, depending only on the local parameters, such that for all such data there is one construction, depending only on the data and not on any input isometry. It consists of a record capacity $C_{\mathrm{cap}}$, signal and work qubits, a set of system qubits, and a unitary circuit $\widehat W_C$ of exact one-qubit unitaries and CNOTs on these logical qubits, with the following properties.
--
--   1. **Logical resources:** $G_{\mathrm{logical,block}}\le C_DZ_*^{10}$ gates, and $Q_{\mathrm{logical,block}}\le C_DZ_*^{6}$ logical qubits (system, environment records, signal and work).
--   2. **Accuracy:** let $Y$ be an isometry from the system into system $\otimes$ all physical baths. Let $Y_{\mathrm{in}}$ be $Y$ followed by the factor's preceding window calls. Suppose every window call has nonnegative bounds $a_b$ on the complete local bath set $B_{\mathrm{cat}}$ with $\sum_b a_b^2\le\nu\Sigma/4$, $\nu=2\cdot 7^D+4$. These bounds must satisfy Eqs. (12)–(14) of Lemma 3.6 for $Y_{\mathrm{in}}$ and every forward prefix $V_{<j}Y_{\mathrm{in}}$ (forward window $V$), or for $V^\dagger Y_{\mathrm{in}}$ and every $V_{<j}V^\dagger Y_{\mathrm{in}}$ (inverse window). Then on the common space
--   $$
--   \bigl\|\bigl[(\widehat W_C)^c-W_C^c\bigr]I_PY\bigr\|\le\eta .
--   $$
--   The common space keeps every physical bath configuration, including occupations above the record capacity.
--   3. **Nearest-neighbour implementation:** for every connected set of $H_{\mathrm{host}}$ grid positions of $\mathbb Z^D$ and every injective placement of the logical qubits on it, there is a circuit of one-qubit unitaries and CNOTs on $\ell^1$-adjacent positions, in layers acting on disjoint positions. Its unitary is $\widehat W_C$ tensored with the identity on the unoccupied positions, and it has
--   $$
--   G_{\mathrm{NN,block}},\ d_{\mathrm{NN,block}}\le C_DH_{\mathrm{host}}Z_*^{10}.
--   $$
--
--   This is the local solver of the paper. Applied to every factor of the localized segment circuit, it gives the logical and routing costs that Theorem 2.1 multiplies by the number of factors and segments.
--
--   **Formalization Note** The record format is fixed by the definitions (label $=$ ordinal $\cdot 2^{\log_2M}+$ period). $C_{\mathrm{cap}}$, the number of work qubits and the system qubits used are chosen by the construction and counted in $Q_{\mathrm{logical,block}}$. The operator-norm bound on $Y$, which maps from the whole system, holds uniformly in an untouched reference.
--
--   Differences from the source:
--   - reading: "a deterministic uniform construction … depend[s] only on these classical data and bounds, not on the ideal input isometry Y" → one construction chosen after the data and bounds and before every Y (by choice, one map from data to circuits), with no running-time clause; reason: the paper attaches no time bound to Theorem 5.1 (the classical-time claim is Theorem 2.1's), and the quantifier order is what makes the circuit independent of Y.
--   - reading: "every prescribed Y whose forward and inverse call families satisfy these common bounds" (Σ bounds the interaction weights) → every isometry Y : system → system ⊗ baths whose call families satisfy Lemma 3.6 on B_cat with one set of a_b ≥ 0 and Σ_b a_b² ≤ νΣ/4; reason: this is the form in which the paper uses Σ (Lemma 3.6, Theorem 3.7), and it covers the prescribed prefix isometries.
--   - reading: v bounds "the number of system qubits, the number of associated terms and the volume of the support box" → d0·|Λ ∩ Ω_C| ≤ v, Σ_A P_A ≤ v over the complete owner blocks, and (9R)^D ≤ v; reason: these are the factor's system qubits (supports of its terms lie in Ω_C), its complete term lists and its support box (p.19).
--   - reading: w_reg bounds "the number of bits allocated to each occurrence address and bath label" → w_{b,A} ≤ w_reg for every complete owner block and ⌈log₂ L⌉ ≤ w_reg for every window call with L occurrences; reason: these are the label width of §5.1 and the address width w = ⌈log₂ L⌉ of the local tree (p.38).
--   - reading: the encoder's bit layout of a bath label → ordinal in the high bits, period in the low log₂ M bits, labels ordered as binary numbers; reason: the page fixes the fields and widths but leaves the layout to "the encoder"; any fixed layout gives the same theorem.
--   - generalization: exact one-qubit rotations together with the paper's elementary multi-qubit gates (X, CNOT, Toffoli, controlled rotations), and for (35) one- and two-qubit nearest-neighbour gates → only one-qubit unitaries and CNOTs, both logically and on the host; reason: Lean claims more (a smaller gate set); each paper gate is an exact product of O(1) such gates, so the paper's statement follows with a larger C_D.
--   - encoding: the common space includes all owners' signal, outer and work registers → only the factor's own signal and work qubits; reason: the others are zero under I_P and untouched by the factor, so no norm changes.
--   - encoding: Σ is a bound on interaction weights → the hypothesis 0 ≤ Σ; reason: interaction weights are nonnegative, so this excludes no instance.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Theorem 5.1, p.37 (pdf p.39); common bounds Eq. (33), p.36; Table 4, p.38; §5.2, Eq. (41), p.42; Table 5, p.43; Eq. (15)–(16), p.20; informal form Theorem D, p.3

import Mathlib
import Definitions.Def_LindbladShallow_Supplement_prescribed
import Definitions.Def_LindbladShallow_Supplement_commonSpace

open scoped Matrix ComplexOrder

namespace LindbladShallow

namespace Supplement

open Classical in
/-- **Theorem 5.1** (Coherent simulation of a local factor; Shen–Wu–Yuan–Zhang, arXiv:2610.05362,
held version sha256 8f4637ef…, p.37, with the common bounds of Eq. (33), p.36, the registers of
§5.1 (Table 4, p.38) and the common space of §5.2 (Eq. (41), Table 5, pp.42–43)).

For fixed local parameters there is a constant `C_D > 0` such that the following holds. Fix a valid
instance, its prescribed execution of §3.3 (`R` of Eq. (11), `r`, `M`, `h = τ/M` of Eq. (15)), an
assigned owner cube `C` with factor `W_C = V^{(c)}_{C,r} ⋯ V^{(c)}_{C,1} V^{(c−1)†}_{C,1} ⋯
V^{(c−1)†}_{C,r}`, and common bounds `v` (support-box volume `(9R)^D`, system qubits of `Ω_C`,
associated terms), `w_reg` (label widths and occurrence-address widths), `Σ ≥ 0`, `0 < η < 1`, with
`Z∗ = 2 + v + w_reg + ⌈Σ⌉ + ⌈log₂(1/η)⌉`. Then there is one construction — a record capacity
`C_cap`, `n_W` signal and work qubits, a set of system qubits and a circuit `Ŵ_C` of exact one-qubit
unitaries and CNOTs on these logical qubits — depending only on these data, with
1. `G_logical,block ≤ C_D Z∗^10` and `Q_logical,block ≤ C_D Z∗^6`;
2. for every isometry `Y` into the physical space whose forward and inverse call families satisfy
   the common bounds (Lemma 3.6 on `B_cat` with one set of `a_b ≥ 0`, `Σ_b a_b² ≤ νΣ/4`,
   `ν = 2·7^D + 4`), `‖[(Ŵ_C)^c − W_C^c] I_P Y‖ ≤ η` on the common space;
3. on every connected host of `H_host` grid positions containing the logical qubits, a
   nearest-neighbour implementation (one-qubit unitaries, CNOTs on ℓ¹-adjacent positions, layers on
   disjoint wires) equal to `Ŵ_C` tensored with the identity, with `G_NN,block, d_NN,block ≤
   C_D H_host Z∗^10`.

**Formalization Note** "Deterministic uniform construction … not on `Y`" is read as one construction
chosen after the classical data and bounds and before `Y` (equivalently, by choice, a map from the
data to circuits); the paper attaches no running-time claim to this theorem. The record format of
the list registers (label = ordinal·2^{log₂ M} + period, value in `log₂ d_E` bits) is fixed by the
definitions; `C_cap` is part of the construction and is charged in `Q_logical`. The other owners'
signal and work registers, initialized to zero by `I_P` and untouched by the factor, are omitted
(this changes no norm). `Y` maps the system into system ⊗ all physical baths, so the operator-norm
bound holds uniformly in an untouched reference. -/
theorem theorem_5_1 :
    ∀ P : Params, ∃ Cst : ℝ, 0 < Cst ∧
    ∀ I : Instance P, I.Valid →
    ∀ C ∈ CLam I (Rlen I),
    ∀ (v wreg : ℕ) (Sig η : ℝ),
      (9 * (Rlen I : ℝ)) ^ P.D ≤ v →
      P.d0 * (Finset.univ.filter fun j : Fin I.n => I.sites.get j ∈ OmegaC I (Rlen I) C).card ≤ v →
      ((blocksOf I (Rlen I) C).sum fun A => (ownerTerms I (Rlen I) A).length) ≤ v →
      (∀ A ∈ blocksOf I (Rlen I) C, wlab I (Mpres I) (Rlen I) A ≤ wreg) →
      (∀ x ∈ factorCalls I (Mpres I) (Rlen I) (rPres I) C, Nat.clog 2 x.2.1.length ≤ wreg) →
      0 ≤ Sig → 0 < η → η < 1 →
      let R := Rlen I
      let M := Mpres I
      let r := rPres I
      let h := hPres I
      let ν : ℝ := 2 * 7 ^ P.D + 4
      let Z : ℝ := 2 + v + wreg + ⌈Sig⌉₊ + ⌈Real.logb 2 (1 / η)⌉₊
      ∃ (Ccap nW : ℕ) (sysW : Finset (Fin I.n × Fin P.d0))
        (gs : List (LGate (LW I M R C Ccap nW sysW))),
        (∀ g ∈ gs, g.Legal) ∧
        (gs.length : ℝ) ≤ Cst * Z ^ 10 ∧
        (Fintype.card (LW I M R C Ccap nW sysW) : ℝ) ≤ Cst * Z ^ 6 ∧
        (∀ Y : Matrix (Tot I M) (Sys I) ℂ, Yᴴ * Y = 1 →
          (∀ (k : ℕ) (hk : k < (factorCalls I M R r C).length),
            let x := (factorCalls I M R r C).get ⟨k, hk⟩
            let Yin := wordU I M h (((factorCalls I M R r C).take k).flatMap callImpl) * Y
            ∃ a : BJ I M → ℝ, (∀ b, 0 ≤ a b) ∧
              ∑ b ∈ Bcat I M R C, a b ^ 2 ≤ ν * Sig / 4 ∧
              ∀ j < max x.2.1.length 1,
                OccBounds (Bcat I M R C) a
                  (if x.2.2 then wordU I M h (x.2.1.take j) * wordU I M h (adjWord x.2.1) * Yin
                   else wordU I M h (x.2.1.take j) * Yin)) →
          opNorm ((unitaryExt (JH I M R C Ccap nW) (liftHw sysW (logicalU gs)) -
              unitaryExt (JP I M R C Ccap nW) (liftPhys (wordU I M h (factorWord I M R C)))) *
              IP I M R C Ccap nW * Y) ≤ η) ∧
        (∀ Hs : Finset (Fin P.D → ℤ),
          ((gridGraph P.D).induce (Hs : Set (Fin P.D → ℤ))).Preconnected →
          ∀ pl : LW I M R C Ccap nW sysW → {x // x ∈ Hs}, Function.Injective pl →
          ∃ layers : List (List (HGate P.D)),
            (∀ L ∈ layers, ∀ g ∈ L, (∀ p ∈ g.wires, p ∈ Hs) ∧
              ((∃ U p, g = .one U p ∧ U ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∨
                (∃ p q, g = .two cxMat p q ∧ p ≠ q ∧ l1dist p q = 1))) ∧
            (∀ L ∈ layers, L.Pairwise fun g g' => ∀ p ∈ g.wires, p ∉ g'.wires) ∧
            hostU Hs layers.flatten = placeU Hs pl (logicalU gs) ∧
            ((layers.map List.length).sum : ℝ) ≤ Cst * Hs.card * Z ^ 10 ∧
            (layers.length : ℝ) ≤ Cst * Hs.card * Z ^ 10) := by sorry

end Supplement

end LindbladShallow
