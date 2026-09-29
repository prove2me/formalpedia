-- Prove2me | Theorems.Thm_IharaTower_exists_rungDatum_two
-- name    : IharaTower.exists_rungDatum_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/7426ac0b-b439-544e-8c52-7f28f93dea60
-- title:
--   A rung datum from the two q-degeneracy legs at level Nq
-- statement:
--   Fix nonzero naturals $N$ and $q$ with $q$ prime and $q \nmid N$, subgroups $H_s \le (\mathbb{Z}/N)^\times$ and $H_s' \le (\mathbb{Z}/Nq)^\times$, and two level data `h1 : LevelLE N (N*q) Hs Hs' 1` and `hq' : LevelLE N (N*q) Hs Hs' q`, each asserting $N \mid Nq$, divisibility of $Nq/N$ by $1$ resp. $q$, and that reduction carries $H_s'$ into $H_s$. Let $\mathcal{O}$ be a commutative ring, $A$ an $\mathcal{O}$-module, and $\mathbb{T}$, $\mathbb{T}'$ commutative $\mathcal{O}$-algebras acting $\mathcal{O}$-compatibly on the carriers $H^1(M,H,A) = \mathrm{Hom}(\Gamma_H(M), A)$ for $(M,H) = (N,H_s)$ and $(Nq,H_s')$. Let `cd`, `cd'` be corner data at these two levels: an idempotent splitting of $\mathbb{T}$ (resp. $\mathbb{T}'$), a chosen index, and a level pairing on the corner ring and the corner submodule $e \cdot H^1$. Assume the two degeneracy maps $\iota_1^*, \iota_q^*$ (`iDegL` for $d = 1, q$) carry the lower corner submodule into the upper one, the two traces $j_q, j_1$ (`jDegL` for $d = q, 1$) carry the upper corner submodule into the lower one, that elements $T_q$, $T_l$ of the lower corner ring act on the corner module as `heckeT N Hs q A` and `heckeTlower N Hs q A`, and that the legs $(\iota_1^*, j_q)$ and $(\iota_q^*, j_1)$ are adjoint for the two corner pairings. Then for every $a$ in the lower corner ring and every $\mathcal{O}$-algebra map $\mathrm{res}$ from the upper to the lower corner ring there is a rung datum $R$ between the two corners (maps $i$, $j$ of $\mathcal{O}$-modules, an element $\Delta$, adjointness of $i$ and $j$, and $j \circ i = \Delta \cdot \mathrm{id}$) with $R.\mathrm{res} = \mathrm{res}$, $R.i(m) = \iota_1^*(a \cdot m) - \iota_q^*(m)$, $R.j(m') = a \cdot j_q(m') - j_1(m')$, and $$R.\Delta = a^2\,[\,\mathrm{im}\,\iota_q : \text{in } \Gamma_H^{\mathrm{up}}(q)\,] \, T_q - a\bigl([\mathrm{im}\,\iota_q] + [\mathrm{im}\,\iota_1]\bigr) + [\,\mathrm{im}\,\iota_1 : \text{in } \Gamma_H^{\mathrm{low}}(q)\,]\, T_l,$$ where the brackets denote the indices of the image of `iotaDeg` in $\Gamma_{H_s}(N)$, resp. of its intersection with `GammaHUpper N Hs q` $= \Gamma_0^{\mathrm{up}}(q) \cap \Gamma_{H_s}(N)$ and with `GammaHLower N Hs q` $= \Gamma_0(qN) \cap \Gamma_{H_s}(N)$, viewed in $\mathcal{O}$ and pushed into the corner ring.
--
--   This is the level-raising step at the auxiliary prime $q$ in the form needed for the Taylor–Wiles patching argument: the two degeneracy maps between levels $N$ and $Nq$, combined with coefficients $(a,-1)$, produce a map of Hecke modules whose composite is multiplication by an explicit element $\Delta$ built from $T_q$, the lower Hecke operator and three subgroup indices. It is used in the construction of Hecke-module rungs at the residue characteristic, where a specialisation of $\Delta$ is shown to be a unit root expression.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_exists_rungDatum_two.lean

import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower IharaTower.CornerData IharaTower.RungAssembly

theorem IharaTower.exists_rungDatum_two (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (Hs : Subgroup (ZMod N)ˣ) (Hs' : Subgroup (ZMod (N * q))ˣ)
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [AddCommGroup A] [Module 𝒪 A]
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (H1 N Hs A)] [Module 𝕋' (H1 (N * q) Hs' A)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs A)] [IsScalarTower 𝒪 𝕋' (H1 (N * q) Hs' A)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs A 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) Hs' A 𝕋')
    (hci : ∀ (k : Fin 2) (v : H1 N Hs A), v ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx) →
      ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k v
        ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx))
    (hcj : ∀ (k : Fin 2) (v' : H1 (N * q) Hs' A),
      v' ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx) →
      ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k v'
        ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx))
    (Tq Tl : cd.cornerRing)
    (hTq : ∀ m : cd.cornerModule, ((Tq • m : cd.cornerModule) : H1 N Hs A) = heckeT N Hs q A (m : H1 N Hs A))
    (hTl : ∀ m : cd.cornerModule, ((Tl • m : cd.cornerModule) : H1 N Hs A) = heckeTlower N Hs q A (m : H1 N Hs A))
    (hadj : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B ⟨![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k m', hcj k _ m'.2⟩ m =
        cd'.pairing.B m' ⟨![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k m, hci k _ m.2⟩)
    (a : cd.cornerRing) (res : cd'.cornerRing →ₐ[𝒪] cd.cornerRing) :
    ∃ R : RungDatum (𝒪 := 𝒪) cd.cornerRing cd'.cornerRing cd.cornerModule cd'.cornerModule cd.pairing cd'.pairing,
      R.res = res ∧
      (∀ m : cd.cornerModule, (R.i m : H1 (N * q) Hs' A) =
        iDegL N (N * q) Hs Hs' 1 A 𝒪 h1 ((a • m : cd.cornerModule) : H1 N Hs A) - iDegL N (N * q) Hs Hs' q A 𝒪 hq' m) ∧
      (∀ m' : cd'.cornerModule, (R.j m' : H1 N Hs A) =
        ((a • (⟨jDegL N (N * q) Hs Hs' q A 𝒪 hq' m', hcj 0 _ m'.2⟩ : cd.cornerModule) : cd.cornerModule) : H1 N Hs A)
          - jDegL N (N * q) Hs Hs' 1 A 𝒪 h1 m') ∧
      R.Δ = a ^ 2 * (algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' q hq').range.subgroupOf (GammaHUpper N Hs q)).index : 𝒪) * Tq)
        - a * (algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' q hq').range.index : 𝒪)
            + algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' 1 h1).range.index : 𝒪))
        + algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' 1 h1).range.subgroupOf (GammaHLower N Hs q)).index : 𝒪) * Tl := by sorry
