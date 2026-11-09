-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_6
-- name    : MWCSherali.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:13:02.642589+00:00
-- url     : https://prove2.me/theorems/dd2681b4-6693-4b73-88cf-31e06c36e339
-- title:
--   Lemma 4.6 — the density vectors are nonnegative and balanced
-- statement:
--   Assume $\beta>0$, $\tfrac12<\alpha\le1-3\beta$ and
--
--   $$4(1-\alpha)^2-24(1-\alpha)\beta+6\beta^2+12\beta-1=0.\tag{17}$$
--
--   Then the choice of parameters
--
--   $$q_c=p_t=\tfrac12,\quad p_c=\frac{2\alpha-2+3\beta}{6(\alpha-1+2\beta)},\quad p_s=\tfrac12-\beta,\quad q_s=1-2\alpha+(4\alpha-1)p_c$$
--
--   defines density vectors (Table 5) with nonnegative entries, and all determinants in Table 6 vanish: for each of the six internal faces $\operatorname{conv}(o,u,w)$ shared by two tetrahedra $T_1,T_2$,
--
--   $$\det\begin{pmatrix}(u_i-o_i)_{i=1,2,3}\\(w_i-o_i)_{i=1,2,3}\\(c^{T_1}_i-c^{T_2}_i)_{i=1,2,3}\end{pmatrix}=0.\tag{16}$$
--
--   The faces and tetrahedra are: $\operatorname{conv}(o,v,v_{34})$ between $\operatorname{conv}(o,h_c,v,v_{34})$ and $\operatorname{conv}(o,h_t,v,v_{34})$; $\operatorname{conv}(o,h_t,v)$ between $\operatorname{conv}(o,h_t,v,v_{12})$ and $\operatorname{conv}(o,h_t,v,v_{34})$; $\operatorname{conv}(o,h_c,v)$ between $\operatorname{conv}(o,h_c,v,v_{23})$ and $\operatorname{conv}(o,h_c,v,v_{34})$; $\operatorname{conv}(o,v,v_{12})$ between $\operatorname{conv}(o,h_s,v,v_{12})$ and $\operatorname{conv}(o,h_t,v,v_{12})$; $\operatorname{conv}(o,v,v_{23})$ between $\operatorname{conv}(o,h_c,v,v_{23})$ and $\operatorname{conv}(o,h_s,v,v_{23})$; $\operatorname{conv}(o,h_s,v)$ between $\operatorname{conv}(o,h_s,v,v_{12})$ and $\operatorname{conv}(o,h_s,v,v_{23})$.
--
--   Vanishing determinants mean the flux of the constant-density flows cancels across every internal face, so only the boundary of $Z$ contributes in Lemma 4.7.
--
--   Differences from the source:
--   - reading: "all determinants in Table 6 are 0" → the determinants (16) for the six internal faces, each with the two tetrahedra sharing it (as listed in Appendix C), computed from the points and density vectors, are 0; reason: Table 6 lists exactly these determinants; its closed forms are the computation of Appendix C (the proof)
--   - encoding: 1-based coordinates and the swaps v_{12}, v_{23}, v_{34} → 0-based coordinates; the swaps exchange Lean coordinates (0,1), (1,2), (2,3); "coordinates 1, 2, 3" are indices 0, 1, 2; reason: Lean convention
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.6, p.39; Table 5, p.38; Table 6, p.40; (16), p.39; Appendix C, pp.58–61

import Mathlib
import Definitions.Def_MWCSherali_CPt
import Definitions.Def_MWCSherali_cpt__6e2ea3
import Definitions.Def_MWCSherali_densTable

namespace MWCSherali

/-- **Lemma 4.6 (the density vectors).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.6, p.39: "Assume that `β > 0`,
`1/2 < α ≤ 1 − 3β`, and `4(1 − α)² − 24(1 − α)β + 6β² + 12β − 1 = 0`. (17) Then, the following
choice of parameters `q_c = p_t = 1/2`, `p_c = (2α − 2 + 3β)/(6(α − 1 + 2β))`, `p_s = 1/2 − β`,
`q_s = 1 − 2α + (4α − 1)p_c`, defines density vectors with nonnegative entries and all
determinants in Table 6 are 0."

The density vectors are those of Table 5 (`densTable`). The determinants of Table 6 (p.40) are
the determinants (16), p.39, `det[(u − o)₁..₃; (w − o)₁..₃; (c^{T₁} − c^{T₂})₁..₃]`, for the six
internal faces `conv(o, u, w)` and the two tetrahedra `T₁, T₂` sharing them (Appendix C):
1. `conv(o, v, v₃₄)`: `conv(o, h_c, v, v₃₄)` and `conv(o, h_t, v, v₃₄)`;
2. `conv(o, h_t, v)`: `conv(o, h_t, v, v₁₂)` and `conv(o, h_t, v, v₃₄)`;
3. `conv(o, h_c, v)`: `conv(o, h_c, v, v₂₃)` and `conv(o, h_c, v, v₃₄)`;
4. `conv(o, v, v₁₂)`: `conv(o, h_s, v, v₁₂)` and `conv(o, h_t, v, v₁₂)`;
5. `conv(o, v, v₂₃)`: `conv(o, h_c, v, v₂₃)` and `conv(o, h_s, v, v₂₃)`;
6. `conv(o, h_s, v)`: `conv(o, h_s, v, v₁₂)` and `conv(o, h_s, v, v₂₃)`.
In the indexing of Table 5 (`tetVerts`, `densTable`) the tetrahedron pairs are
`(1,5), (4,5), (0,1), (2,4), (0,3), (2,3)`.

**Formalization Note.** The determinant is computed from the points and vectors (not from
Table 6's closed forms, which are the proof). "The first three coordinates" are Lean indices
`0, 1, 2` (the paper's `1, 2, 3`); points and vectors are in 0-based coordinates (`cpt`). -/
theorem lemma_4_6 (α β : ℝ) (hβ : 0 < β) (hα : 1 / 2 < α) (hαβ : α ≤ 1 - 3 * β)
    (h17 : 4 * (1 - α) ^ 2 - 24 * (1 - α) * β + 6 * β ^ 2 + 12 * β - 1 = 0) :
    let pc := (2 * α - 2 + 3 * β) / (6 * (α - 1 + 2 * β))
    let c := densTable pc (1 / 2) (1 / 2 - β) (1 - 2 * α + (4 * α - 1) * pc) (1 / 2)
    let faces : List (CPt × CPt × Fin 6 × Fin 6) :=
      [(.v, .v34, 1, 5), (.ht, .v, 4, 5), (.hc, .v, 0, 1), (.v, .v12, 2, 4),
        (.v, .v23, 0, 3), (.hs, .v, 2, 3)]
    (∀ r i, 0 ≤ c r i) ∧
      ∀ F ∈ faces,
        Matrix.det (Matrix.of ![fun m : Fin 3 => cpt α β F.1 m.castSucc - cpt α β .o m.castSucc,
          fun m : Fin 3 => cpt α β F.2.1 m.castSucc - cpt α β .o m.castSucc,
          fun m : Fin 3 => c F.2.2.1 m.castSucc - c F.2.2.2 m.castSucc]) = 0 := by sorry

end MWCSherali
