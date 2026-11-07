-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_4_3
-- name    : OWFLocalDesc.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:07.424204+00:00
-- url     : https://prove2.me/theorems/b3a29bd9-1f3a-49ba-b6a2-f9e71fed5abc
-- title:
--   Theorem 4.3 (Small-bias spaces, cited from Alon–Goldreich–Håstad–Peralta)
-- statement:
--   There are a seed-length function $h(L,\varepsilon)$, maps $S_{L,\varepsilon}:\{0,1\}^{h(L,\varepsilon)}\to\mathbb F_2^L$ and a constant $C$ such that for every positive integer $L$ and every rational $0<\varepsilon<1$:
--
--   1. $h(L,\varepsilon)\le C\,\big(1+\log L+\log(1/\varepsilon)\big)$;
--   2. $S_{L,\varepsilon}$ has bias at most $\varepsilon$: $\big|\mathbb E_{z\sim U_h}(-1)^{\langle v,S_{L,\varepsilon}(z)\rangle}\big|\le\varepsilon$ for every nonzero $v\in\mathbb F_2^L$;
--   3. the map is uniform: one algorithm computes the full vector $S_{L,\varepsilon}(z)$ from $L$, the rational $\varepsilon$ and the seed $z$ in time polynomial in $L$, $1/\varepsilon$ and the binary encoding length of $\varepsilon$;
--   4. the seed length $h(L,\varepsilon)$ is computed by one such algorithm as well.
--
--   The hardness proof uses $S$ to turn each query point into a linear measurement of a planted vector.
--
--   **Formalization Note** $L$ and $\lceil 1/\varepsilon\rceil$ are given in unary next to the binary code of $\varepsilon$, so "polynomial in $L$ and $1/\varepsilon$" is polynomial in the input length.
--
--   Differences from the source:
--   - reading: h = O(1 + log L + log(1/ε)) → h(L,ε) ≤ C(1 + log L + log(1/ε)) for all admissible (L, ε), one constant C; reason: O-notation in two parameters is ambiguous; this is the stronger reading, and the construction on p.18 gives h ≤ 2 log(L/ε) + 2 everywhere
--   - reading: the seed-length schedule is uniform → h(L,ε) is computed (in unary) by one polynomial-time machine from (1^L, 1^⌈1/ε⌉, ε); reason: the stronger reading; the paper's preprocessing for ω = ⌈log(L/ε)⌉ is polynomial time (p.18)
--   - encoding: computing the full vector takes time polynomial in L, 1/ε and the binary encoding length of ε → one `CookPvsNP.PolyTimeComputable` machine on the code of (1^L, 1^⌈1/ε⌉, binary ε, seed); 𝔽₂ = `ZMod 2`; reason: unary L and ⌈1/ε⌉ make the paper's time bound polynomial in the input length
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.3, p.17 (cited from [AGHP92, Construction 3 and Proposition 3])

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_HasBiasAtMost
import Definitions.Def_OWFLocalDesc_ratCode
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 4.3 (Small-bias spaces), cited from [AGHP92].** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Theorem 4.3, p.17: "For every positive integer L and rational 0 < ε < 1, the following construction
exists [AGHP92, Construction 3 and Proposition 3]. There is an explicitly computable map
S : {0,1}^h → F_2^L, with h = O(1 + log L + log(1/ε)), such that |E_{z∼U_h} (−1)^{⟨v,S(z)⟩}| ≤ ε for
every nonzero v ∈ F_2^L. The map and its seed-length schedule are uniform. Given L, the rational ε
and the seed, computing the full vector takes time polynomial in L, 1/ε and the binary encoding
length of ε."

**Formalization Note.** One seed-length function `h(L, ε)` and one map `S` for all `(L, ε)`;
`h = O(1 + log L + log(1/ε))` is read with one constant `C` for all admissible `(L, ε)` (the
construction on p.18 gives `h ≤ 2 log(L/ε) + 2` everywhere). "Uniform" and the running time are
one polynomial-time machine on the code of `(1^L, 1^{⌈1/ε⌉}, ε, seed)` (resp. without the seed for
the seed length, written in unary): unary `L` and `⌈1/ε⌉` make "polynomial in `L` and `1/ε`"
polynomial in the input length. -/
theorem theorem_4_3 :
    ∃ (h : ℕ → ℚ → ℕ) (S : (L : ℕ) → (ε : ℚ) → (Fin (h L ε) → Bool) → (Fin L → ZMod 2)) (C : ℝ),
      (∀ (L : ℕ) (ε : ℚ), 0 < L → 0 < ε → ε < 1 →
        (h L ε : ℝ) ≤ C * (1 + Real.logb 2 L + Real.logb 2 (1 / (ε : ℝ)))) ∧
      (∀ (L : ℕ) (ε : ℚ), 0 < L → 0 < ε → ε < 1 → HasBiasAtMost (S L ε) (ε : ℝ)) ∧
      (∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧
        ∀ (L : ℕ) (ε : ℚ), 0 < L → 0 < ε → ε < 1 → ∀ z : Fin (h L ε) → Bool,
          g (QuantumPRC.tupleCode [QuantumPRC.unary L, QuantumPRC.unary ⌈1 / ε⌉₊, ratCode ε,
            List.ofFn z]) = vecBits (S L ε z)) ∧
      (∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧
        ∀ (L : ℕ) (ε : ℚ), 0 < L → 0 < ε → ε < 1 →
          g (QuantumPRC.tupleCode [QuantumPRC.unary L, QuantumPRC.unary ⌈1 / ε⌉₊, ratCode ε]) =
            QuantumPRC.unary (h L ε)) := by sorry

end OWFLocalDesc
