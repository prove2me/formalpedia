-- Prove2me | Theorems.Thm_LindbladShallow_corollary_3_5
-- name    : LindbladShallow.corollary_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:22:47.194003+00:00
-- url     : https://prove2.me/theorems/a72678f5-f2c4-4cb7-b7af-5124bdc75391
-- title:
--   Corollary 3.5 — parallel local decomposition
-- statement:
--   Fix the fixed parameters. There is a constant $C'>0$ such that for every valid input, with $N_0,\tau,m_*,R$ of Eq. (11) and $\chi=8^D$:
--
--   1. there are at most $n$ regional factors: $|C_\Lambda|\le n$, and their colours lie in $\{1,\dots,\chi\}$ ($\chi$ parallel layers);
--   2. for every number of periods $M\ge1$ (step $h=\tau/M$) and every order of the owners within a colour, $\|(W_{\mathrm{loc}}-U_\chi)E_0\|\le\epsilon/(16N_0)$;
--   3. each factor's envelope $\Omega_C$ has $\ell^\infty$ diameter at most $C'(1+\log X)$;
--   4. distinct owners of the same colour have disjoint complete hosts $RC+[-3R,4R)^D$.
--
--   Here $W_{\mathrm{loc}}=D^{\mathrm{loc}}_\chi\cdots D^{\mathrm{loc}}_1$, $D^{\mathrm{loc}}_c=\prod_{\mathrm{colour}(C)=c}W_C$ and $W_C=U_{c,\Omega_C}U_{c-1,\Omega_C}^\dagger$.
--
--   This turns each segment into a constant number of layers of polylogarithmic-size local factors, which is what yields nearly linear gate count and depth.
--
--   Differences from the source:
--   - reading: support diameter O_D(1 + log X) → ∃ C' > 0, chosen after the fixed parameters and before the input, bounding the ℓ∞ diameter of every envelope Ω_C; reason: the factor W_C acts on the system sites of Ω_C; O_D means a constant depending on the fixed parameters
--   - reading: uniform in the collision mesh → for every M ≥ 1 with h = τ/M; reason: the collision mesh is the number of periods of a segment
--   - reading: W_loc consists of at most n regional factors in χ = 8^D parallel layers → |C_Λ| ≤ n and every owner colour lies in {1, …, χ}; reason: the factors are indexed by C_Λ and the layers by the colours
--   - reading: colours modulo eight → colour(C) = 1 + Σ_j (C_j mod 8)·8^j; reason: one fixed enumeration of (ℤ/8)^D; the page fixes none
--   - generalization: the prescribed owner order → every order of the owners within a colour; reason: same-colour factors act on disjoint supports and baths; the source's order is one of them
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Corollary 3.5, p.18; construction pp.17–18, Eq. (11)

import Mathlib
import Definitions.Def_LindbladShallow_localDecomp

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- **Corollary 3.5** (Parallel local decomposition; arXiv:2610.05362, held version
sha256 8f4637ef…, p.18, with the construction of pp.17–18 and Eq. (11)). With
`N₀ = max{1, ⌈4096κa⌉}`, `τ = T/N₀`, `m∗ = 1 + ⌈log₈(4096χ²nN₀²/ϵ²)⌉`, `R = 2r∗m∗`, the localized
segment circuit `W_loc = D_χ^loc ⋯ D_1^loc`, `D_c^loc = ∏_{colour(C)=c} W_C`,
`W_C = U_{c,Ω_C}U_{c−1,Ω_C}†`, consists of at most `n` regional factors (`|C_Λ| ≤ n`) in
`χ = 8^D` parallel layers (colours) and satisfies `‖(W_loc − U_χ)E₀‖ ≤ ϵ/(16N₀)`. The factors have
support diameter `O_D(1 + log X)` and disjoint complete hosts within each layer. The estimate is
uniform in the collision mesh (every `M ≥ 1`, `h = τ/M`) and an untouched reference.

**Formalization Note** `O_D(1 + log X)` is an explicit constant `C'` chosen after the fixed
parameters and before the input. The owners of one colour may be taken in any order `ord` (they act
on disjoint supports and baths). The complete host of `C` is the box `RC + [−3R, 4R)^D`. -/
theorem corollary_3_5 :
    ∀ P : Params, ∃ C' : ℝ, 0 < C' ∧ ∀ I : Instance P, I.Valid →
      let R := Rlen I
      (CLam I R).card ≤ I.n ∧
      (∀ C ∈ CLam I R, 1 ≤ colour C ∧ colour C ≤ chi P) ∧
      (∀ M : ℕ, 1 ≤ M → ∀ ord : List (Fin P.D → ℤ), ord.Nodup → (∀ C, C ∈ ord ↔ C ∈ CLam I R) →
        opNorm ((wordU I M (tau I / M) (locWord I M R ord) -
            collU I M (tau I / M) (actUpTo I R (chi P)) Set.univ) * E0 I M) ≤
          (I.ε : ℝ) / (16 * N0 I)) ∧
      (∀ C ∈ CLam I R, ∀ x ∈ OmegaC I R C, ∀ y ∈ OmegaC I R C, ∀ j,
        (|x j - y j| : ℝ) ≤ C' * (1 + Real.log (bigX I))) ∧
      (∀ C ∈ CLam I R, ∀ C₂ ∈ CLam I R, C ≠ C₂ → colour C = colour C₂ →
        Disjoint (hostC R C) (hostC R C₂)) := by sorry

end LindbladShallow
