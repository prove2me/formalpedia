-- Prove2me | Theorems.Thm_FourMsgQMA_theorem_3_23
-- name    : FourMsgQMA.theorem_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:35:16.673806+00:00
-- url     : https://prove2.me/theorems/8198aac9-1294-4c97-b2d7-7da50082beaa
-- title:
--   Theorem 3.23 — index and vector batch arguments from LWE
-- statement:
--   This is Theorem 3.23 (index and vector arguments from LWE) in the pinned-down version requested by the operator.
--
--   Fix $\varepsilon\in(0,1)$ and assume $\mathrm{Hyp}(\varepsilon)$. Then both of the following hold.
--
--   1. The **index** interface of §3.11.1 has an instantiation with perfect completeness, index hiding and semi-adaptive extraction (Definition 3.22). Its CRS, trapdoor and proof lengths and its verification and extraction cost are $\mathrm{poly}(\lambda,S,m,\log(k+1))$, and setup and proving are polynomial time.
--   2. The **vector** interface of §3.11 has an instantiation with perfect completeness, index hiding (Definition 3.20) and semi-adaptive somewhere extraction (Definition 3.21). Its lengths are $\mathrm{poly}(\lambda,s_R,\log(k+1))$ and its algorithms are polynomial time.
--
--   In both interfaces the circuit or instance vector may be chosen after setup, while the bounds and the extraction coordinate are fixed before it.
--
--   The construction of §5.1 proves all $k$ local relations $C_\theta(i,w_i)$ with one index BARG. Its extraction at $i^*$ recovers the local witness of the target coordinate.
--
--   Differences from the source:
--   - reading: "post-quantum LWE at parameters supporting the CJJ construction [CJJ22, Sections 4.3–4.4]" → Hyp(ε) for the given ε ∈ (0,1): LWE (Assumption 3.10's game) for every efficiently computable (n, q, σ) with polynomial n ≥ max(λ,1), 2 ≤ q ≤ 2^{n^ε}, discrete Gaussian error D_{ℤ,σ} with σ ≥ 2√n; reason: the paper fixes no family ("Each instantiation specifies its family", p.15); it keeps a superpolynomial modulus-to-noise ratio (p.14) and GSW needs q > 8(M+1)^L B with dimension and log q polynomial (p.18), i.e. ratio 2^{poly}; σ ≥ 2√n is Regev's regime
--   - reading: "the index and vector interfaces above" → each interface with its completeness, security and succinctness/efficiency paragraphs (§3.11, p.20; §3.11.1, p.21); reason: the interfaces are defined with these clauses
--   - encoding: circuits C : [k] × {0,1}^m → {0,1} and relations R(u, w) → NandCircuit on the ⌈log₂(k+1)⌉-bit binary index followed by the witness (resp. on u ++ w); an adversary's circuit description is parsed with the inverse of NandCircuit.encode and an unparsable one is rejected; reason: Lean representation; "Invalid encodings are rejected" (p.21)
--   - encoding: "every QPT adversary selecting a valid index" → an invalid index is read as 1; reason: an adversary naming an invalid index is simulated by one naming index 1
--   - reading: PPT / deterministic classical algorithms and their running times → QAlgorithms.Complexity.PolyTimeComputable maps of the packed inputs with explicit uniform coins; per-instance work as Boolean circuit size (ComputedOn); reason: the paper's machine model is informal (§3.3); this is the standard uniform model
--   - encoding: QPT adversaries and distinguishers: nonuniform polynomial-size quantum circuit families with one quantum advice state (§3.1, p.9) → the published TightPQRepetition.Main.IsQPT strategies and IsQTestFamily distinguishers (gate set: all one- and two-qubit unitaries), on both sides of the implication; reason: a finite universal gate set approximates these circuits to negligible error at polynomial cost (Solovay–Kitaev), so the classes give the same negligible-advantage statements
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 3.23, p.21 (PDF 23)

import Mathlib
import Definitions.Def_FourMsgQMA_LWEHyp
import Definitions.Def_FourMsgQMA_IndexBARG

namespace FourMsgQMA

/-- **Theorem 3.23** (Index and vector arguments from LWE), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.21 (PDF 23), pinned-down version (operator request).

For every `ε ∈ (0, 1)`, under `Hyp(ε)`:
1. the index interface of §3.11.1 has an instantiation with the efficiency of p.21, perfect
   completeness, index hiding and semi-adaptive extraction (Definition 3.22);
2. the vector interface of §3.11 has an instantiation with the succinctness of p.20, perfect
   completeness, index hiding (Definition 3.20) and semi-adaptive somewhere extraction
   (Definition 3.21).
In both, the circuit or instance vector is chosen after setup, and the bounds and the extraction
coordinate before it.

**Formalization Note** "post-quantum LWE at parameters supporting the CJJ construction" is read as
`Hyp(ε)`. -/
theorem theorem_3_23 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hLWE : LWEHyp ε) :
    (∃ B : IndexBARG, B.Efficient ∧ B.PerfectlyComplete ∧ B.Secure) ∧
      (∃ B : VectorBARG, B.Efficient ∧ B.PerfectlyComplete ∧ B.Secure) := by sorry

end FourMsgQMA
