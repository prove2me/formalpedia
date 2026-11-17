-- Prove2me | Theorems.Thm_ModLatSVP_Supplement_theorem_3_1
-- name    : ModLatSVP.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:19:59.792195+00:00
-- url     : https://prove2.me/theorems/45771359-4208-4918-81e1-cd30bf615c83
-- title:
--   Theorem 3.1, p.17 — rank-one SVP and ball enumeration along a supplied subfield chain, with factors $F_j=2^{O(D_j)}$ and polynomial space
-- statement:
--   Fix integers $s_0\ge2$, $d_0\ge1$ and a rational $C_0\ge1$. Suppose the input supplies a chain of totally real or CM fields
--
--   $$K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h,\qquad [K_j:K_{j+1}]\le s_0,\quad [K_h:\mathbb Q]\le d_0,\quad \mathrm{rd}(K_0)\le C_0,$$
--
--   with integral bases, multiplication tables, inclusions and involutions $\star$, and write $D_j=[K_j:\mathbb Q]$. For a rank-one $\mathcal O_{K_j}$-module $L$ and $\varrho\ge0$ put $A(L,\varrho)=\max\{1,\varrho/\lambda_1(L)\}$. Then there are two deterministic algorithms, uniform over all levels $0\le j\le h$, and a constant $C$ depending only on $s_0,d_0,C_0$, such that, with $F_j=2^{C D_j}$:
--
--   1. $\mathsf{SV}_j(L)$ returns a shortest nonzero vector of $L$ in time $F_j\,\mathrm{poly}(\ell)$;
--   2. $\mathsf{EN}_j(L,c,\varrho)$, for a rational centre $c$ and rational $\varrho^2\ge0$, outputs every point of $L$ in the ball $B(c,\varrho)$, each once, in time $F_j\,A(L,\varrho)^{D_j}\,\mathrm{poly}(\ell)$;
--
--   both in polynomial working space, where $\ell$ is the input length (field data, chain data, the level $j$, the module and, for $\mathsf{EN}_j$, the centre and $\varrho^2$). With one constant $C$, $F_h\le2^{Cd_0}=O(1)$ and $F_j\le2^{CD_j}F_{j+1}$, which is the last sentence of the theorem.
--
--   These are the rank-one subroutines that Algorithm 1 needs; by subfield descent they cost single-exponential time at every level of the chain.
--
--   **Formalization Note** The algorithms are TM2 machines with the base mission's time ($\texttt{SpikyCVP.RunsWithin}$) and working-space ($\texttt{ModLatSVP.SpaceWithin}$) conventions; one machine of each kind and one pair of polynomial degrees serve every level and every chain. Level $0$ is described by $K_0$'s own field data, level $j\ge1$ by the $j$-th supplied level. The chain fields being totally real or CM and of root discriminant at most $C_0$ follow from the hypotheses on $K_0$ and are not assumed.
--
--   Differences from the source:
--   - reading: the routines "can be implemented with factors F_j = 2^{O(D_j)}, depending only on s_0, d_0, C_0" (no machine named) → TM2 machines M_SV, M_EN and constants C, k, k' chosen after s_0, d_0, C_0 and before the field, chain, level and module, with F_j = 2^{C·D_j}; reason: the paper fixes no machine (same reading as the published Theorem 3.4); one C makes F_h = O(1) and F_j ≤ 2^{O(D_j)}F_{j+1} hold, so the last sentence is implied
--   - reading: poly(B, N) and poly(B, N, ℓ(c, ϱ^2)) → (ℓ+1)^k with ℓ the length of the routine's whole input (field data, chain data, j, module, and c, ϱ^2 for EN); reason: B and the module size are at most ℓ; standalone the routine has no other input
--   - reading: EN_j "streams all points of L ∩ B(c, ϱ)" → outputs a duplicate-free list whose members are exactly the x ∈ ℤ^{D_j} with (x − c)ᵀG(x − c) ≤ ϱ^2; reason: streaming the points of a set lists each point once (Lemma 3.2 outputs each point exactly once)
--   - encoding: rank-one 𝒪_{K_j}-module L with chain data → ℤ^{D_j} with Gram G and integer action matrices of the level-j integral basis, compatible with ⋆ (RepresentsRankOne); level 0 described by K_0's own data (topLevel); reason: input model of §2.2 at level j
--   - encoding: rd(K_0) ≤ C_0; chain of totally real or CM fields → |Δ_K| ≤ C_0^{[K:ℚ]}; K_0 totally real or CM, the subfields not assumed so; reason: same condition without real roots; subfields of a totally real or CM field are so (ModLatSVP.subfield_star)
--   - encoding: polynomial working space → SpaceWithin: all stacks but the output stack, output append-only, bound (ℓ+1)^{k'}; reason: same model as the published Theorems 3.4 and 3.5
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Theorem 3.1 and the setting of §3.1, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_SpikyCVP_RunsWithin
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_IsStar
import Definitions.Def_ModLatSVP_lam1
import Definitions.Def_ModLatSVP_RepresentsChain
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest
import Definitions.Def_ModLatSVP_SpaceWithin
import Definitions.Def_ModLatSVP_Supplement_RepresentsRankOne

open NumberField ExponomialAssortment.FPTAS

namespace ModLatSVP

namespace Supplement

/-- **Theorem 3.1, §3.1, p.17: rank-one SVP and ball enumeration by subfield descent.** Kim, Lee, Son,
*Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027
submission (manuscript sha256 e7151fad…). Setting (p.17): "Fix integers s₀ ≥ 2 and d₀ ≥ 1, and a rational
constant C₀ ≥ 1. Suppose we are given a chain of totally real or CM fields K₀ ⊋ K₁ ⊋ ⋯ ⊋ K_h,
[K_j : K_{j+1}] ≤ s₀, [K_h : ℚ] ≤ d₀, rd(K₀) ≤ C₀, together with integral bases, multiplication tables,
inclusions, and involutions ⋆ compatible with these inclusions. The chain data are included in the input
length B." "SV_j(L) returns a shortest nonzero vector of L. EN_j(L, c, ϱ) streams all points of
L ∩ B(c, ϱ), where c has rational coordinates and ϱ ≥ 0 has rational square." "For a rank-one module L,
set A(L, ϱ) = max{1, ϱ/λ₁(L)}." Theorem 3.1: "The routines SV_j and EN_j can be implemented with factors
F_j = 2^{O(D_j)}, depending only on s₀, d₀, C₀, such that SV_j(L) takes time F_j poly(B, N) and
EN_j(L, c, ϱ) takes time F_j A(L, ϱ)^{D_j} poly(B, N, ℓ(c, ϱ²)). Both routines use polynomial working
space. The polynomial factors and space bounds are uniform over all field levels (Lemma 3.3). Moreover,
F_h = O(1) and F_j ≤ 2^{O(D_j)} F_{j+1} for j < h."

There are two TM2 machines `M_SV`, `M_EN` and constants `C, k, k'`, depending only on `s₀, d₀, C₀`, such
that for every totally real or CM field `K = K₀` with `rd(K) ≤ C₀`, field data `(d, c, S)`, every chain
`F` of subfields described by the supplied levels `Ls` (`h = |Ls|`), every level `j ≤ h` with data `L`
(`L = K₀`'s own data for `j = 0`, the `j`-th supplied level otherwise; `D_j = L.e`) and every rank-one
`𝒪_{K_j}`-module `(G, A')` on `ℤ^{D_j}`, with input `ℓ` bits long (field data, chain data, `j`, module,
and for `EN` also the centre `c'` and `ϱ²`):
1. `M_SV` outputs a shortest nonzero vector within `2^{C D_j} (ℓ+1)^k` steps, in working space `(ℓ+1)^{k'}`;
2. `M_EN` outputs, each exactly once, all `x ∈ ℤ^{D_j}` with `(x − c')ᵀ G (x − c') ≤ ϱ²`, within
   `2^{C D_j} A(L, ϱ)^{D_j} (ℓ+1)^k` steps, in working space `(ℓ+1)^{k'}`.

**Formalization Note.**
* `F_j = 2^{O(D_j)}`, "depending only on `s₀, d₀, C₀`", is `2^{C·D_j}` with one `C`; then `F_h ≤ 2^{C d₀}
  = O(1)` and `F_j ≤ 2^{C D_j} F_{j+1}` hold, so the last sentence of the theorem is implied.
* "Uniform over all field levels": one machine of each kind, one `C`, one pair of degrees `k, k'` for
  every level `j` and every chain.
* Machine, time and space as in `ModLatSVP.theorem_3_4`; `ℓ` is the length of the routine's whole input,
  which contains the chain data (`B`) and the module (`D_j ≤ N`), so `poly(B, N)` is `poly(ℓ)`.
* The chain's fields being totally real or CM, and `rd(K_j) ≤ C₀`, are not assumed: they follow from the
  hypotheses on `K₀` (`ModLatSVP.subfield_star`, `ModLatSVP.eq_11`).
* `A(L, ϱ)` is real; the step count is compared with the real bound. -/
theorem theorem_3_1 (d₀ s₀ : ℕ) (hd₀ : 1 ≤ d₀) (hs₀ : 2 ≤ s₀) (C₀ : ℚ) (hC₀ : 1 ≤ C₀) :
    ∃ (Msv Men : Turing.TM2ComputableAux Bool Bool) (C k k' : ℕ),
      ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃ₐ[ℚ] K) (d : ℕ) (ω : Fin d → K)
        (c : Fin d → Fin d → Fin d → ℤ) (S : Matrix (Fin d) (Fin d) ℤ)
        (F : ℕ → IntermediateField ℚ K) (Ls : List (FieldLevel d)) (j : ℕ) (L : FieldLevel d)
        (G : Matrix (Fin L.e) (Fin L.e) ℚ) (A' : Fin L.e → Matrix (Fin L.e) (Fin L.e) ℤ),
        (IsTotallyReal K ∨ IsCMField K) → |(discr K : ℝ)| ≤ (C₀ : ℝ) ^ Module.finrank ℚ K →
        IsStar K τ → RepresentsField K τ ω c S →
        IsChain K s₀ d₀ F Ls.length → RepresentsChainAt K τ ω F Ls →
        (topLevel c S :: Ls)[j]? = some L →
        RepresentsRankOne K τ (F j) (levelBasis ω L) G A' →
        ((∃ x : Fin L.e → ℤ, IsShortest G x ∧
            SpikyCVP.RunsWithin Msv
              (encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                (List.finRange L.e).flatMap (fun a => encIntMat (A' a)))
              (encIntVec x)
              (2 ^ (C * L.e) *
                ((encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                  (List.finRange L.e).flatMap (fun a => encIntMat (A' a))).length + 1) ^ k)) ∧
          SpaceWithin Msv
            (encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
              (List.finRange L.e).flatMap (fun a => encIntMat (A' a)))
            (((encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
              (List.finRange L.e).flatMap (fun a => encIntMat (A' a))).length + 1) ^ k')) ∧
        ∀ (c' : Fin L.e → ℚ) (ϱsq : ℚ), 0 ≤ ϱsq →
          (∃ xs : List (Fin L.e → ℤ), xs.Nodup ∧
              (∀ x, x ∈ xs ↔ qfQ G ((fun i => (x i : ℚ)) - c') ≤ ϱsq) ∧
              SpikyCVP.RunsWithin Men
                (encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                  (List.finRange L.e).flatMap (fun a => encIntMat (A' a)) ++
                  SpikyCVP.encVec c' ++ encodeRat ϱsq)
                (xs.flatMap encIntVec)
                ⌊(2 : ℝ) ^ (C * L.e) *
                    (max 1 (Real.sqrt (ϱsq : ℝ) / lam1 (G.map (fun q : ℚ => (q : ℝ))))) ^ L.e *
                    (((encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                      (List.finRange L.e).flatMap (fun a => encIntMat (A' a)) ++
                      SpikyCVP.encVec c' ++ encodeRat ϱsq).length : ℝ) + 1) ^ k⌋₊) ∧
            SpaceWithin Men
              (encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                (List.finRange L.e).flatMap (fun a => encIntMat (A' a)) ++
                SpikyCVP.encVec c' ++ encodeRat ϱsq)
              (((encField d c S ++ encChain Ls ++ encodeNat j ++ SpikyCVP.encMat G ++
                (List.finRange L.e).flatMap (fun a => encIntMat (A' a)) ++
                SpikyCVP.encVec c' ++ encodeRat ϱsq).length + 1) ^ k') := by sorry

end Supplement

end ModLatSVP
