-- Prove2me | Theorems.Thm_FourMsgQMA_proposition_3_19
-- name    : FourMsgQMA.proposition_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:57.687022+00:00
-- url     : https://prove2.me/theorems/ccc5ac82-b1e6-422c-b1ae-2bb77a7069ca
-- title:
--   Proposition 3.19 — block commitments from FHE (Hubáček–Wichs)
-- statement:
--   This is Proposition 3.19 (Hubáček–Wichs, [HW15]) in the pinned-down version requested by the operator.
--
--   Let $\mathrm{FHE}$ be a leveled FHE scheme with polynomial-time algorithms, the compactness of §3.9, uniform correctness (Definition 3.14) and post-quantum IND-CPA security (Definition 3.15). Then there is a somewhere-extractable block commitment $\mathrm{SC}$ with all of the following properties:
--
--   1. perfect completeness;
--   2. statistical extraction consistency (Definition 3.18, strong form);
--   3. post-quantum index hiding (Definition 3.17);
--   4. public keys, trapdoors, digests and openings of length $\mathrm{poly}(\lambda,m,\log(k+1))$, with local verification and extraction of the same size;
--   5. setup, commitment and opening in time $\mathrm{poly}(\lambda,k,m)$.
--
--   The construction of §5.1 uses $\mathrm{SC}$ to commit to the selected first base-protocol responses $(\mu_i)_{i\in[k]}$. Its trapdoor lets the soundness reduction extract the target's response before the challenge.
--
--   Differences from the source:
--   - reading: "Uniformly correct compact FHE with post-quantum IND-CPA security" → FHE.IsUniform ∧ FHE.Compact ∧ FHE.UniformlyCorrect ∧ FHE.INDCPA; reason: "compact" refers to the paragraph "Compactness and efficiency" of §3.9, which includes the running times
--   - reading: "block commitments" with the listed properties → the full §3.10 interface, including the trapdoor-length and opening-time clauses of its Succinctness paragraph; reason: the proposition instantiates the interface of §3.10; stating every clause of that interface is the stronger reading
--   - reading: "statistical extraction consistency" → the strong form of Definition 3.18, with α and ρ ranging over all strings; reason: p.19: "We use the stronger statistical property"; Verify rejects malformed encodings, so all strings is the same as the prescribed encodings
--   - encoding: indices i ∈ [k] and "A choosing valid indices" (Definition 3.17) → natural numbers 1 ≤ i ≤ k; in the hiding game an invalid index is read as 1; reason: an adversary naming an invalid index is simulated by one naming index 1
--   - reading: PPT / deterministic classical algorithms and their running times → QAlgorithms.Complexity.PolyTimeComputable maps of the packed inputs with explicit uniform coins; per-instance work as Boolean circuit size (ComputedOn); reason: the paper's machine model is informal (§3.3); this is the standard uniform model
--   - encoding: QPT adversaries and distinguishers: nonuniform polynomial-size quantum circuit families with one quantum advice state (§3.1, p.9) → the published TightPQRepetition.Main.IsQPT strategies and IsQTestFamily distinguishers (gate set: all one- and two-qubit unitaries), on both sides of the implication; reason: a finite universal gate set approximates these circuits to negligible error at polynomial cost (Solovay–Kitaev), so the classes give the same negligible-advantage statements
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Proposition 3.19, p.19 (PDF 21)

import Mathlib
import Definitions.Def_FourMsgQMA_FHE
import Definitions.Def_FourMsgQMA_SEC

namespace FourMsgQMA

/-- **Proposition 3.19** (Hubáček–Wichs [HW15]), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.19 (PDF 21), pinned-down version (operator request).

Every leveled FHE scheme with polynomial-time algorithms, the compactness of §3.9, uniform
correctness (Definition 3.14) and post-quantum IND-CPA security (Definition 3.15) gives a
somewhere-extractable block commitment with perfect completeness, statistical extraction
consistency (Definition 3.18, strong form), post-quantum index hiding (Definition 3.17), keys,
digests and openings of length `poly(λ, m, log(k+1))`, local verification and extraction of the
same size, and setup, commitment and opening in time `poly(λ, k, m)`.

**Formalization Note** "Uniformly correct compact FHE" includes the efficiency requirements of
§3.9 (`FHE.IsUniform`). -/
theorem proposition_3_19 (E : FHE) (hU : E.IsUniform) (hC : E.Compact) (hCor : E.UniformlyCorrect)
    (hCPA : E.INDCPA) :
    ∃ S : SEC, S.IsUniform ∧ S.PerfectlyComplete ∧ S.StatExtractConsistent ∧ S.IndexHiding ∧
      S.Succinct := by sorry

end FourMsgQMA
