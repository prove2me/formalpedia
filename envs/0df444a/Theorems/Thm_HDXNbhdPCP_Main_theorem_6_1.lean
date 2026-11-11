-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_theorem_6_1
-- name    : HDXNbhdPCP.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:51.773165+00:00
-- url     : https://prove2.me/theorems/fa112923-39d6-4d63-a4bb-b158db25986f
-- title:
--   Theorem 6.1 — a sparse, strongly explicit family of sound projective neighbourhood tests
-- statement:
--   There is an absolute constant $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every $\eta\in(0,1)$, every prime $q\ge\mathrm{poly}(1/\varepsilon,1/\eta)$ and every integer $N\ge1$ there is a strongly explicit pure 4-partite complex $X$ with:
--
--   1. **Size and sparsity.** $N\le|X[2]\sqcup X[3]|\le N\cdot\mathrm{poly}(q)$, and every vertex belongs to at most $\mathrm{poly}(q)$ nonempty faces.
--   2. **Expansion and sampling.** $X[2,3]$ is a $\mathrm{poly}(q)$-regular balanced bipartite graph; each of $X[2,3]$, $X[1,\{2,3\}]$, $X[\{2,3\},4]$ is an $O(q^{-1/2})$-expander; the neighbourhoods indexed by $X[1]$ and by $X[4]$ are $O(q^{-1})$-samplers of the edges of $X[2,3]$.
--   3. **Agreement and projection.** The neighbourhood test on $X\langle2\sqcup3\rangle$, with universe $X[2]\sqcup X[3]$, is $(\varepsilon,\eta,\Omega(1),O(1))$-sound and projective.
--   4. **Strong explicitness.** Vertices have names of $O(\log|X[2]\sqcup X[3]|)$ bits; the faces incident to a vertex can be listed deterministically in $q^{O(1)}\mathrm{poly}(\log|X[2]\sqcup X[3]|)$ time; the whole complex can be constructed deterministically in $\mathrm{poly}(N,q)$ time.
--
--   All constants and polynomials are independent of $N,q,\varepsilon,\eta$. In symbols, with $M=|X[2]\sqcup X[3]|$:
--   $$N\le M\le N\,K_p q^{k_p},\qquad X[2,3],\ X[1,\{2,3\}],\ X[\{2,3\},4]\ \text{are } K_x q^{-1/2}\text{-expanders},\qquad T_{X\langle2\sqcup3\rangle}\ (\varepsilon,\eta,c_0,e_0)\text{-sound}.$$
--
--   This is the agreement tester on which the PCP of Theorem 1.1 is built.
--
--   Differences from the source:
--   - reading: 'there is a strongly explicit … complex X' for each (ε, η, q, N); 'constructed deterministically in poly(N, q) time' → one family X N q independent of ε and η, one construction algorithm buildFn on (N, q) and one listing algorithm listFn, each with a polynomial-time TM2 machine; reason: the construction reads only N and q, and 'strongly explicit' is a property of a uniform algorithm
--   - reading: the constructed complex's distribution (unstated) → uniform on its facets (FinDist.Same X (uniform X.supp)), facets = buildFn's output; reason: the paper's X is a regrouped coset complex whose facet law is uniform; 'constructing the complex' then means listing its facets
--   - reading: 'the latter two graphs are O(q^{-1})-samplers: the neighborhoods indexed by X[1] and X[4] sample the edges of X[2, 3]' → IsSampler for X[{2,3}, 1] and X[{2,3}, 4] (functions on {2,3}-faces averaged over neighbourhoods of colour-1 or colour-4 vertices); reason: the explanatory clause fixes the direction; it is the use in Lemma 7.3
--   - encoding: names of O(log |X[2] ⊔ X[3]|) bits; time q^{O(1)} poly(log |X[2] ⊔ X[3]|); time poly(N, q) → vertices are bit strings of length ≤ K_n (⌊log₂ M⌋ + 1); listFn polynomial-time with N in binary and q in unary; buildFn polynomial-time with N, q in unary; reason: with q in unary and N in binary, polynomial time in the input length is q^{O(1)} poly(log M) because log N ≤ log M
--   - encoding: poly(1/ε, 1/η), poly(q), O(q^{-1/2}), O(q^{-1}), Ω(1), O(1) → P₀ (ε⁻¹η⁻¹)^{k₀}, K_p q^{k_p}, K_x q^{-1/2}, K_x q^{-1}, c₀ > 0, e₀ > 0, all chosen before ε, η, q, N; reason: explicit existential constants in the paper's order
--   - encoding: colours 1, 2, 3, 4; X⟨2 ⊔ 3⟩ with universe X[2] ⊔ X[3] → Fin 4 colours 0, …, 3; merge X 1 2 with the test on colours (some 0, none, some 3); reason: Lean convention; same test
--   - encoding: a nonempty finite alphabet Σ → a type Sig : Type with Fintype (and Nonempty where the source asks for it); reason: every finite alphabet is in bijection with a type in Type 0
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 38, Theorem 6.1 (proved in §6.5, pp. 44-46)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Agreement
import Definitions.Def_HDXNbhdPCP_Main_Encoding

namespace HDXNbhdPCP.Main

/-- Theorem 6.1 (a sparse family of projection neighbourhood tests). Colours `0, 1, 2, 3` are the
paper's `1, 2, 3, 4`; vertices are their names (bit strings). The complex `X N q` is the one built
for target size `N` and prime `q`; `buildFn` and `listFn` are the deterministic polynomial-time
algorithms of item 4. -/
theorem theorem_6_1 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∃ P₀ : ℝ, ∃ k₀ : ℕ, ∃ Kp : ℝ, ∃ kp : ℕ, ∃ Kx : ℝ, ∃ c₀ e₀ : ℝ, 0 < c₀ ∧ 0 < e₀ ∧ ∃ Kn : ℝ,
    ∃ X : ℕ → ℕ → ColoredComplex (Fin 4) (fun _ => List Bool),
    ∃ listFn : ℕ × ℕ × Fin 4 × List Bool → List Face4,
    ∃ buildFn : ℕ × ℕ → List (Fin 4 → List Bool),
      Nonempty (Turing.TM2ComputableInPolyTime encListInput encFaceList listFn) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encBuildInput encFacetList buildFn) ∧
      ∀ ε η : ℝ, 0 < ε → ε < ε₀ → 0 < η → η < 1 →
      ∀ q : ℕ, q.Prime → (q : ℝ) ≥ P₀ * (ε⁻¹ * η⁻¹) ^ k₀ →
      ∀ N : ℕ, 1 ≤ N →
        FinDist.IsProb (X N q) ∧
        -- 1. size and sparsity
        N ≤ ((X N q).vertices 1).card + ((X N q).vertices 2).card ∧
        ((((X N q).vertices 1).card + ((X N q).vertices 2).card : ℕ) : ℝ) ≤
          N * (Kp * (q : ℝ) ^ kp) ∧
        (∀ i : Fin 4, ∀ v ∈ (X N q).vertices i,
          ((incidentFaces (X N q) i v).card : ℝ) ≤ Kp * (q : ℝ) ^ kp) ∧
        -- 2. expansion and sampling
        (∃ D : ℕ, (D : ℝ) ≤ Kp * (q : ℝ) ^ kp ∧ ((X N q).pairGraph 1 2).IsRegular D ∧
          ((X N q).pairGraph 1 2).IsBalanced) ∧
        ((X N q).pairGraph 1 2).IsExpander (Kx * (q : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ((X N q).setPairGraph {0} {1, 2}).IsExpander (Kx * (q : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ((X N q).setPairGraph {1, 2} {3}).IsExpander (Kx * (q : ℝ) ^ (-(1 / 2 : ℝ))) ∧
        ((X N q).setPairGraph {1, 2} {0}).IsSampler (Kx * (q : ℝ)⁻¹) ∧
        ((X N q).setPairGraph {1, 2} {3}).IsSampler (Kx * (q : ℝ)⁻¹) ∧
        -- 3. agreement and projection: the neighbourhood test on `X⟨2 ⊔ 3⟩`
        (((X N q).merge 1 2).nbhdTestOn (some ⟨0, by decide⟩) none
            (some ⟨3, by decide⟩)).IsSound ε η c₀ e₀ ∧
        (((X N q).merge 1 2).nbhdTestOn (some ⟨0, by decide⟩) none
            (some ⟨3, by decide⟩)).IsProjective ∧
        -- 4. strong explicitness
        (∀ i : Fin 4, ∀ v ∈ (X N q).vertices i, (v.length : ℝ) ≤
          Kn * (Nat.log 2 (((X N q).vertices 1).card + ((X N q).vertices 2).card) + 1)) ∧
        (∀ i : Fin 4, ∀ v ∈ (X N q).vertices i,
          (listFn (N, q, i, v)).toFinset = incidentFaces (X N q) i v) ∧
        (buildFn (N, q)).toFinset = (X N q).supp ∧
        FinDist.Same (X N q) (FinDist.uniform (X N q).supp) := by sorry

end HDXNbhdPCP.Main
