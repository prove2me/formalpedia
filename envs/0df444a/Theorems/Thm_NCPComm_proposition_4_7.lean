-- Prove2me | Theorems.Thm_NCPComm_proposition_4_7
-- name    : NCPComm.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:04:24.086204+00:00
-- url     : https://prove2.me/theorems/3c2ce00c-9cca-424f-a26e-b81eaa3ef131
-- title:
--   Proposition 4.7 — reducing from disjointness to NCP
-- statement:
--   Let $N\in3\mathbb N$, $K=N^k$ with $k\in(0.5,1)$, and let $s\ge C_1\sqrt N$ for a sufficiently large absolute constant $C_1$, with $s=o(\min\{K,N/\sqrt K\})$. Let Alice and Bob hold $a,b\in\{0,1\}^N$ with $|b|=N-K$ and $|a|=\lfloor\frac{s^2}{64K}e^{-s/(4K)}\rfloor$, and share public randomness. The zero-communication setup of Figure 4.9.1 gives Alice vectors $u_1,\dots,u_{s'}$ on non-abort and gives Bob vectors $p_{\mathrm{heavy}},p_{\mathrm{light}}\in\{0,1\}^{2N}$, such that, with abort a separate outcome:
--
--   1. if $\langle a,b\rangle=0$, then
--   $$
--   \delta_{\mathrm{TV}}\Big(\big((p_{\mathrm{light}},p_{\mathrm{heavy}}),(u_i)_i\big),\big((\mathbf P^0_{\mathrm{light}},\mathbf P^0_{\mathrm{heavy}}),(\mathbf V^0_i)_i\big)(2N,2K,s')\Big)=o(1);
--   $$
--   2. if $\langle a,b\rangle=g(N,K,s):=\Big\lfloor\frac{s^2}4\Big(\frac{e^{-\frac{s}{2(2N/3-2K)}}}{2(2N/3-2K)}-\frac{e^{-\frac{s}{2(2N-2K)}}}{2(2N-2K)}\Big)+\frac12\Big\rfloor=\Theta(s^2/N)$, then the distribution described by $(p_{\mathrm{heavy}},p_{\mathrm{light}})$ belongs to $\mathcal F_0(2N,2K)$, and
--   $$
--   \delta_{\mathrm{TV}}\big((u_i)_i,(\mathbf V^1_i)_i(2N,2K,s')\big)\le0.27,
--   $$
--   and the same bound holds jointly with $p_{\mathrm{heavy}}$ on the left and $\mathbf P^1_{\mathrm{heavy}}$ on the right.
--
--   This is the central step: the prover's information is always from the YES family, while the verifier's sample is close to a YES sample or a NO sample according to whether the inputs are disjoint.
--
--   **Formalization Note** The first bound is uniform over promised inputs, by a sequence $\varepsilon(n)\to0$ chosen before $a,b$.
--
--   Differences from the source:
--   - encoding: D uniform on F_b(N, K) → π uniform on permutations, D = π(D_b); reason: the orbit map pushes the uniform law to the uniform law on the orbit; the page reads the randomness as "the heavy and light sets"
--   - encoding: asymptotic statement in N with o(·), O(·), Ω(·) → sequences N(n), K(n), s(n) with limits and "for all large n"; reason: decision 11 of the plan; a family of parameters is what the asymptotic notation quantifies over
--   - encoding: multiplicity indicators (v_i)_i → the count function on labels, with v_i(x) = 1 iff the count at x is i; reason: the two determine each other, and s′ is the total of the counts
--   - generalization: K = N^k for k ∈ (0.5, 1), with 0 < K < N/3 standing (p.19) → √N < K < N and 3K < N for all large n, with no fixed k; reason: the proof uses only K = o(N), s = o(K) and s = o(N/√K), which the regime implies; a fixed k is a special case
--   - generalization: "there exists a 0-communication setup procedure" → the statement for the procedure of Figure 4.9.1 itself; reason: the printed procedure is the witness, and it reads each input only on its own side; existence follows
--   - encoding: "the distribution described by (p_heavy, p_light)" → the D with mass 1/(4K) on p_heavy and 1/(2(2N−2K)) elsewhere, for every value of π; reason: F₀(2N, 2K) has exactly these two masses, and p_light is the complement of p_heavy by construction
--   - reading: g(N, K, s) = Θ(s²/N) with constants unnamed on the page → ∃ c, C absolute, quantified with C₁ before the sequences, with the bounds for all large n; reason: the stronger reading; the bracket is s²/(8N)(1 + o(1)) and s²/N ≥ C₁², so the floor stays within absolute factors
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Proposition 4.7, p.21

import Mathlib
import Definitions.Def_NCPComm_setupProcedure

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Proposition 4.7 (Reducing from disjointness to NCP), p.21** (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).
There is an absolute `C₁` such that, for source parameters `N = 3n`, `K`, `s` in the regime of the
Proposition, the zero-communication procedure of Figure 4.9.1 satisfies the following, on inputs with
`|a| = ⌊(s²/(64K)) e^{-s/(4K)}⌋` and `|b| = N - K`, abort being a separate outcome:
1. if `⟨a, b⟩ = 0`, the joint output is `o(1)`-close to the ideal YES setup at `(2N, 2K)`, uniformly
   over the inputs;
2. if `⟨a, b⟩ = g(N, K, s)`, Bob's output describes a distribution in `F₀(2N, 2K)` for every value of
   the shared randomness, and Alice's output is within `0.27` of the ideal NO sample, also jointly
   with `p_heavy`;
3. `g(N, K, s) = Θ(s²/N)`.

**Formalization Note** This is stated for the procedure of Figure 4.9.1 itself, which is stronger
than the page's "there exists". Bob's distribution assigns `1/(4K)` to `p_heavy` and `1/(2(2N-2K))`
elsewhere. The ideal side never aborts, so abort is charged in full. The constants `c, C` of
`g = Θ(s²/N)` are absolute, quantified with `C₁` before the sequences; the `o(1)` sequence `ε` and
the thresholds in `n` depend on the sequence. -/
theorem proposition_4_7 :
    ∃ C₁ c C : ℝ, 0 < C₁ ∧ 0 < c ∧ 0 < C ∧ ∀ (K : ℕ → ℕ) (s : ℕ → ℝ≥0), InRegime C₁ K s →
      (∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
        ∀ a b : Fin (3 * n) → Bool, weight a = inputSizeA (K n) (s n) → weight b = 3 * n - K n →
          innerCount a b = 0 →
          OAI.ThreeState.tvMass (setupProcedure (3 * n) (K n) (s n) a b)
              ((idealSetup false (2 * (3 * n)) (2 * K n) (s n)).map some)
            ≤ ε n) ∧
      (∀ᶠ n in atTop,
        ∀ a b : Fin (3 * n) → Bool, weight a = inputSizeA (K n) (s n) → weight b = 3 * n - K n →
          innerCount a b = gapG (3 * n) (K n) (s n) →
          (∀ π : Equiv.Perm (Fin (2 * (3 * n))),
            ∃ D ∈ family false (2 * (3 * n)) (2 * K n), ∀ x,
              D x = if bobHeavy (3 * n) (K n) b π x = true then ((2 * (2 * K n) : ℕ) : ℝ≥0∞)⁻¹
                else ((2 * (2 * (3 * n) - 2 * K n) : ℕ) : ℝ≥0∞)⁻¹) ∧
          OAI.ThreeState.tvMass
              ((setupProcedure (3 * n) (K n) (s n) a b).map (Option.map fun o => o.counts))
              ((idealSetup true (2 * (3 * n)) (2 * K n) (s n)).map fun o => some o.counts)
            ≤ 0.27 ∧
          OAI.ThreeState.tvMass
              ((setupProcedure (3 * n) (K n) (s n) a b).map
                (Option.map fun o => (o.heavy, o.counts)))
              ((idealSetup true (2 * (3 * n)) (2 * K n) (s n)).map fun o =>
                some (o.heavy, o.counts))
            ≤ 0.27) ∧
      (∀ᶠ n in atTop,
        c * ((s n : ℝ) ^ 2 / (3 * n)) ≤ (gapG (3 * n) (K n) (s n) : ℝ) ∧
        (gapG (3 * n) (K n) (s n) : ℝ) ≤ C * ((s n : ℝ) ^ 2 / (3 * n))) := by sorry

end NCPComm
